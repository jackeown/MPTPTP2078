%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eE93U2ysrB

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  70 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  507 ( 921 expanded)
%              Number of equality atoms :   41 (  77 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X41: $i,X43: $i,X44: $i] :
      ( ( k2_zfmisc_1 @ X44 @ ( k2_xboole_0 @ X41 @ X43 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X44 @ X41 ) @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_enumset1 @ X28 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('13',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['1','2','11','12'])).

thf('14',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X41 @ X43 ) @ X42 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X41 @ X42 ) @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('16',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

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
    inference(simpl_trail,[status(thm)],['14','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eE93U2ysrB
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:40:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 21 iterations in 0.014s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.44  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.44  thf(t132_zfmisc_1, conjecture,
% 0.21/0.44    (![A:$i,B:$i,C:$i]:
% 0.21/0.44     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.44         ( k2_xboole_0 @
% 0.21/0.44           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.21/0.44           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.21/0.44       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.21/0.44         ( k2_xboole_0 @
% 0.21/0.44           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.21/0.44           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.44        ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.44            ( k2_xboole_0 @
% 0.21/0.44              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.21/0.44              ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.21/0.44          ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.21/0.44            ( k2_xboole_0 @
% 0.21/0.44              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.21/0.44              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t132_zfmisc_1])).
% 0.21/0.44  thf('0', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.44          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.44              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))
% 0.21/0.44        | ((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.44            != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.44                (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('1', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.44          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.44              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))
% 0.21/0.44         <= (~
% 0.21/0.44             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.44                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.44                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.21/0.44      inference('split', [status(esa)], ['0'])).
% 0.21/0.44  thf(t120_zfmisc_1, axiom,
% 0.21/0.44    (![A:$i,B:$i,C:$i]:
% 0.21/0.44     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.21/0.44         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.21/0.44       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.44         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      (![X41 : $i, X43 : $i, X44 : $i]:
% 0.21/0.44         ((k2_zfmisc_1 @ X44 @ (k2_xboole_0 @ X41 @ X43))
% 0.21/0.44           = (k2_xboole_0 @ (k2_zfmisc_1 @ X44 @ X41) @ 
% 0.21/0.44              (k2_zfmisc_1 @ X44 @ X43)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.21/0.44  thf(t77_enumset1, axiom,
% 0.21/0.44    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (![X28 : $i, X29 : $i]:
% 0.21/0.44         ((k2_enumset1 @ X28 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.21/0.44      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.21/0.44  thf(t71_enumset1, axiom,
% 0.21/0.44    (![A:$i,B:$i,C:$i]:
% 0.21/0.44     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.44  thf('4', plain,
% 0.21/0.44      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.44         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.21/0.44           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.21/0.44      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.44  thf('5', plain,
% 0.21/0.44      (![X28 : $i, X29 : $i]:
% 0.21/0.44         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.21/0.44      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.44  thf(t69_enumset1, axiom,
% 0.21/0.44    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.44  thf('6', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.21/0.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.44  thf('7', plain,
% 0.21/0.44      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.44      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.44  thf(t46_enumset1, axiom,
% 0.21/0.44    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.44     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.44       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.21/0.44  thf('8', plain,
% 0.21/0.44      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.44         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.21/0.44           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ (k1_tarski @ X5)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.21/0.44  thf('9', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.21/0.44           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.44      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.44  thf('10', plain,
% 0.21/0.44      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.44         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.21/0.44           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.21/0.44      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.44  thf('11', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.21/0.44           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.44      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.44  thf('12', plain,
% 0.21/0.44      (![X28 : $i, X29 : $i]:
% 0.21/0.44         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.21/0.44      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.44  thf('13', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.44          != (k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.21/0.44         <= (~
% 0.21/0.44             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.44                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.44                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.21/0.44      inference('demod', [status(thm)], ['1', '2', '11', '12'])).
% 0.21/0.44  thf('14', plain,
% 0.21/0.44      (($false)
% 0.21/0.44         <= (~
% 0.21/0.44             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.44                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.44                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.21/0.44      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.44  thf('15', plain,
% 0.21/0.44      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.44         ((k2_zfmisc_1 @ (k2_xboole_0 @ X41 @ X43) @ X42)
% 0.21/0.44           = (k2_xboole_0 @ (k2_zfmisc_1 @ X41 @ X42) @ 
% 0.21/0.44              (k2_zfmisc_1 @ X43 @ X42)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.21/0.44  thf('16', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.44          != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.44              (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))
% 0.21/0.44         <= (~
% 0.21/0.44             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.44                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.44                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.21/0.44      inference('split', [status(esa)], ['0'])).
% 0.21/0.44  thf('17', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.44          != (k2_zfmisc_1 @ 
% 0.21/0.44              (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ sk_C)))
% 0.21/0.44         <= (~
% 0.21/0.44             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.44                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.44                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.21/0.44      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.44  thf('18', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.21/0.44           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.44      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.44  thf('19', plain,
% 0.21/0.44      (![X28 : $i, X29 : $i]:
% 0.21/0.44         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.21/0.44      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.44  thf('20', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.44          != (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 0.21/0.44         <= (~
% 0.21/0.44             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.44                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.44                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.21/0.44      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.44  thf('21', plain,
% 0.21/0.44      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.44          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.44             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.21/0.44      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.44  thf('22', plain,
% 0.21/0.44      (~
% 0.21/0.44       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.44          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.44             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))) | 
% 0.21/0.44       ~
% 0.21/0.44       (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.44          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.21/0.44             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.21/0.44      inference('split', [status(esa)], ['0'])).
% 0.21/0.44  thf('23', plain,
% 0.21/0.44      (~
% 0.21/0.44       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.44          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.21/0.44             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))),
% 0.21/0.44      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.21/0.44  thf('24', plain, ($false),
% 0.21/0.44      inference('simpl_trail', [status(thm)], ['14', '23'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
