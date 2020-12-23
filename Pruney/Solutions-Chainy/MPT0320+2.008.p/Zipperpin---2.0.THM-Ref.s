%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OarTljhLXt

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  34 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  386 ( 601 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t132_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
        & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_zfmisc_1])).

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ ( k2_xboole_0 @ X2 @ X4 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X2 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('4',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ ( k2_zfmisc_1 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('10',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['5','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OarTljhLXt
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:40:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 6 iterations in 0.011s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(t132_zfmisc_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.46         ( k2_xboole_0 @
% 0.20/0.46           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.20/0.46           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.20/0.46       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.20/0.46         ( k2_xboole_0 @
% 0.20/0.46           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.20/0.46           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.46        ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.46            ( k2_xboole_0 @
% 0.20/0.46              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.20/0.46              ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.20/0.46          ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.20/0.46            ( k2_xboole_0 @
% 0.20/0.46              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.20/0.46              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t132_zfmisc_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.46          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.46              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))
% 0.20/0.46        | ((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.46            != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.46                (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.46          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.46              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.46                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.46                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf(t120_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.20/0.46         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.20/0.46       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.46         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         ((k2_zfmisc_1 @ X5 @ (k2_xboole_0 @ X2 @ X4))
% 0.20/0.46           = (k2_xboole_0 @ (k2_zfmisc_1 @ X5 @ X2) @ (k2_zfmisc_1 @ X5 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.20/0.46  thf(t41_enumset1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k2_tarski @ A @ B ) =
% 0.20/0.46       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k2_tarski @ X0 @ X1)
% 0.20/0.46           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.46          != (k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.46                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.46                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.20/0.46      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (($false)
% 0.20/0.46         <= (~
% 0.20/0.46             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.46                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.46                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.46         ((k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X4) @ X3)
% 0.20/0.46           = (k2_xboole_0 @ (k2_zfmisc_1 @ X2 @ X3) @ (k2_zfmisc_1 @ X4 @ X3)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.46          != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.46              (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.46                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.46                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.46          != (k2_zfmisc_1 @ 
% 0.20/0.46              (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ sk_C)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.46                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.46                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k2_tarski @ X0 @ X1)
% 0.20/0.46           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.46          != (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.46                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.46                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.20/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.46          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.46             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (~
% 0.20/0.46       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.46          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.46             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))) | 
% 0.20/0.46       ~
% 0.20/0.46       (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.46          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.46             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (~
% 0.20/0.46       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.46          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.46             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain, ($false),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['5', '13'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
