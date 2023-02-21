structure Timer where
  interval : Float
  current : Float
deriving Inhabited

def Timer.new (interval : Float) : Timer where
  interval := interval
  current := 0.0

private partial
def Timer.react (timer : Timer) [Monad m] [Nonempty (m (Timer × α))] (f : α → m α) (x : α) : m (Timer × α) :=
  if timer.current < timer.interval
    then pure (timer, x)
    else do {
      let x' ← f x
      { timer with current := timer.current - timer.interval }.react f x'
    }

def Timer.update (timer : Timer) (deltaTime : Float) (x0 : α) [Monad m] [Nonempty (m (Timer × α))] (f : α → m α) : m (Timer × α) :=
  { timer with current := timer.current + deltaTime }.react f x0
