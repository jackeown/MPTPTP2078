%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nDYsc6xRAb

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  72 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  512 ( 949 expanded)
%              Number of equality atoms :   41 (  79 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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
    ! [X29: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ X32 @ ( k2_xboole_0 @ X29 @ X31 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X32 @ X29 ) @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['1','2','13'])).

thf('15',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X29 @ X31 ) @ X30 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('17',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,(
    ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['15','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nDYsc6xRAb
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 21 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.47  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(t132_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.47         ( k2_xboole_0 @
% 0.21/0.47           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.21/0.47           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.21/0.47       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.21/0.47         ( k2_xboole_0 @
% 0.21/0.47           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.21/0.47           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.47            ( k2_xboole_0 @
% 0.21/0.47              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.21/0.47              ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.21/0.47          ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.21/0.47            ( k2_xboole_0 @
% 0.21/0.47              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.21/0.47              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t132_zfmisc_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.47          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.47              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))
% 0.21/0.47        | ((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47            != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.47                (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.47          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.47              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.47                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.47                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf(t120_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.21/0.47         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.21/0.47       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.47         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.21/0.47         ((k2_zfmisc_1 @ X32 @ (k2_xboole_0 @ X29 @ X31))
% 0.21/0.47           = (k2_xboole_0 @ (k2_zfmisc_1 @ X32 @ X29) @ 
% 0.21/0.47              (k2_zfmisc_1 @ X32 @ X31)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.21/0.47  thf(t69_enumset1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.47  thf('3', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.21/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.47  thf(t77_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X23 : $i, X24 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X23 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.21/0.47      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.21/0.47  thf(t71_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.21/0.47           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X23 : $i, X24 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(t46_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.47       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X8 @ X9 @ X10 @ X11)
% 0.21/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X9 @ X10) @ (k1_tarski @ X11)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.21/0.47           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.21/0.47           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X1 @ X0 @ X2)
% 0.21/0.47           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['3', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X23 : $i, X24 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k2_tarski @ X0 @ X1)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.47          != (k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.47                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.47                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.21/0.47      inference('demod', [status(thm)], ['1', '2', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (($false)
% 0.21/0.47         <= (~
% 0.21/0.47             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.47                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.47                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.47         ((k2_zfmisc_1 @ (k2_xboole_0 @ X29 @ X31) @ X30)
% 0.21/0.47           = (k2_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 0.21/0.47              (k2_zfmisc_1 @ X31 @ X30)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47          != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.47              (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.47                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47          != (k2_zfmisc_1 @ 
% 0.21/0.47              (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.47                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k2_tarski @ X0 @ X1)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47          != (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.47                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.21/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.47             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (~
% 0.21/0.47       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.47          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.47             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))) | 
% 0.21/0.47       ~
% 0.21/0.47       (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.47             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (~
% 0.21/0.47       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.47          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.47             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, ($false),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['15', '23'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
