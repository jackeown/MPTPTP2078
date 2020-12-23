%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.guduLFYzoZ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  55 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  362 ( 698 expanded)
%              Number of equality atoms :   28 (  56 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t82_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r1_tarski @ A @ B )
       => ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
            = ( k7_relat_1 @ C @ A ) )
          & ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r1_tarski @ A @ B )
         => ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
              = ( k7_relat_1 @ C @ A ) )
            & ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
              = ( k7_relat_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ( ( k7_relat_1 @ X10 @ X11 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X7 @ X6 ) @ X5 )
        = ( k7_relat_1 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('15',plain,
    ( ( ( ( k7_relat_1 @ sk_C @ sk_A )
       != ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k7_relat_1 @ sk_C @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('20',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['10','20'])).

thf('22',plain,
    ( ( ( k7_relat_1 @ sk_C @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k7_relat_1 @ sk_C @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.guduLFYzoZ
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 26 iterations in 0.027s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(t82_funct_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.48         ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.19/0.48             ( k7_relat_1 @ C @ A ) ) & 
% 0.19/0.48           ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.19/0.48             ( k7_relat_1 @ C @ A ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48          ( ( r1_tarski @ A @ B ) =>
% 0.19/0.48            ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.19/0.48                ( k7_relat_1 @ C @ A ) ) & 
% 0.19/0.48              ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.19/0.48                ( k7_relat_1 @ C @ A ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t82_funct_1])).
% 0.19/0.48  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t87_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]:
% 0.19/0.48         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X9)) @ X9)
% 0.19/0.48          | ~ (v1_relat_1 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.19/0.48  thf(t1_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.48       ( r1_tarski @ A @ C ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.48          | ~ (r1_tarski @ X1 @ X2)
% 0.19/0.48          | (r1_tarski @ X0 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X1)
% 0.19/0.48          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.19/0.48          | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)) @ sk_B)
% 0.19/0.48          | ~ (v1_relat_1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.48  thf(t97_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.48         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.19/0.48          | ((k7_relat_1 @ X10 @ X11) = (X10))
% 0.19/0.48          | ~ (v1_relat_1 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X0)
% 0.19/0.48          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A))
% 0.19/0.48          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B)
% 0.19/0.48              = (k7_relat_1 @ X0 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf(dt_k7_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B)
% 0.19/0.48            = (k7_relat_1 @ X0 @ sk_A))
% 0.19/0.48          | ~ (v1_relat_1 @ X0))),
% 0.19/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.19/0.48          != (k7_relat_1 @ sk_C @ sk_A))
% 0.19/0.48        | ((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.48            != (k7_relat_1 @ sk_C @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.19/0.48          != (k7_relat_1 @ sk_C @ sk_A)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.19/0.48                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t103_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ C ) =>
% 0.19/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.48         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X5 @ X6)
% 0.19/0.48          | ~ (v1_relat_1 @ X7)
% 0.19/0.48          | ((k7_relat_1 @ (k7_relat_1 @ X7 @ X6) @ X5)
% 0.19/0.48              = (k7_relat_1 @ X7 @ X5)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t103_relat_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.19/0.48            = (k7_relat_1 @ X0 @ sk_A))
% 0.19/0.48          | ~ (v1_relat_1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.48          != (k7_relat_1 @ sk_C @ sk_A)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.48                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (((((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))
% 0.19/0.48         | ~ (v1_relat_1 @ sk_C)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.48                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.48                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.48          = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (~
% 0.19/0.48       (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.19/0.48          = (k7_relat_1 @ sk_C @ sk_A))) | 
% 0.19/0.48       ~
% 0.19/0.48       (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.48          = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (~
% 0.19/0.48       (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.19/0.48          = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.19/0.48         != (k7_relat_1 @ sk_C @ sk_A))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['10', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      ((((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '21'])).
% 0.19/0.48  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
