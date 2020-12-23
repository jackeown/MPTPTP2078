%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2LPaUepYok

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  61 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  324 ( 453 expanded)
%              Number of equality atoms :   36 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t124_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
        = ( k2_zfmisc_1 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
          = ( k2_zfmisc_1 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t124_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X40 @ X42 ) @ ( k3_xboole_0 @ X41 @ X43 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ X1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_D ) @ sk_D ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_D ) @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_C )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','15','16','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2LPaUepYok
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 58 iterations in 0.033s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(t124_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.20/0.48       ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.20/0.48         ( k2_zfmisc_1 @ A @ C ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.20/0.48          ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.20/0.48            ( k2_zfmisc_1 @ A @ C ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t124_zfmisc_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 0.20/0.48         (k2_zfmisc_1 @ sk_B @ sk_C)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ 
% 0.20/0.48         (k2_zfmisc_1 @ sk_A @ sk_D)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t12_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.48  thf('5', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf(t95_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k3_xboole_0 @ A @ B ) =
% 0.20/0.48       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         ((k3_xboole_0 @ X9 @ X10)
% 0.20/0.48           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.20/0.48         = (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((k3_xboole_0 @ sk_B @ sk_A)
% 0.20/0.48         = (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(t91_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.48       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.48           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.48  thf(t92_xboole_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('11', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.48  thf(t5_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('12', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.48  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.20/0.48  thf(t123_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.20/0.48       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.48         ((k2_zfmisc_1 @ (k3_xboole_0 @ X40 @ X42) @ (k3_xboole_0 @ X41 @ X43))
% 0.20/0.48           = (k3_xboole_0 @ (k2_zfmisc_1 @ X40 @ X41) @ 
% 0.20/0.48              (k2_zfmisc_1 @ X42 @ X43)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.48           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ X1) @ 
% 0.20/0.48              (k2_zfmisc_1 @ sk_A @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf('17', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.48  thf('19', plain, (((k2_xboole_0 @ sk_C @ sk_D) = (sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         ((k3_xboole_0 @ X9 @ X10)
% 0.20/0.48           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((k3_xboole_0 @ sk_C @ sk_D)
% 0.20/0.48         = (k5_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_D) @ sk_D))),
% 0.20/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((k3_xboole_0 @ sk_D @ sk_C)
% 0.20/0.48         = (k5_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_D) @ sk_D))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.48           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.48  thf('25', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.48  thf('26', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.48  thf('27', plain, (((k3_xboole_0 @ sk_D @ sk_C) = (sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (((k2_zfmisc_1 @ sk_A @ sk_C) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '15', '16', '27'])).
% 0.20/0.48  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
