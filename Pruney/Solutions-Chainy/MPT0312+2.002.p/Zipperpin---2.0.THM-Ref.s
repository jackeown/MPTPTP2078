%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1vbjkMPcnP

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  360 ( 564 expanded)
%              Number of equality atoms :   42 (  64 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X37 @ X39 ) @ ( k3_xboole_0 @ X38 @ X40 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = ( k5_xboole_0 @ sk_D @ ( k5_xboole_0 @ sk_D @ sk_C ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_C )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','1','18','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1vbjkMPcnP
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:10:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 96 iterations in 0.045s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(t124_zfmisc_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.22/0.50       ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.22/0.50         ( k2_zfmisc_1 @ A @ C ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.22/0.50          ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.22/0.50            ( k2_zfmisc_1 @ A @ C ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t124_zfmisc_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 0.22/0.50         (k2_zfmisc_1 @ sk_B @ sk_C)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t123_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.22/0.50       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.22/0.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ X37 @ X39) @ (k3_xboole_0 @ X38 @ X40))
% 0.22/0.50           = (k3_xboole_0 @ (k2_zfmisc_1 @ X37 @ X38) @ 
% 0.22/0.50              (k2_zfmisc_1 @ X39 @ X40)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.22/0.50  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t12_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.50  thf('4', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(t95_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k3_xboole_0 @ A @ B ) =
% 0.22/0.50       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]:
% 0.22/0.50         ((k3_xboole_0 @ X11 @ X12)
% 0.22/0.50           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.22/0.50              (k2_xboole_0 @ X11 @ X12)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.22/0.50  thf(commutativity_k5_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]:
% 0.22/0.50         ((k3_xboole_0 @ X11 @ X12)
% 0.22/0.50           = (k5_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ 
% 0.22/0.50              (k5_xboole_0 @ X11 @ X12)))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.22/0.50         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['4', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.22/0.50         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf(t92_xboole_1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('11', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.50  thf(t91_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.50       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.22/0.50           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.50           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.50  thf(t5_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('15', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.50  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['13', '16'])).
% 0.22/0.50  thf('18', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '17'])).
% 0.22/0.50  thf('19', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.50  thf('21', plain, (((k2_xboole_0 @ sk_C @ sk_D) = (sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf(commutativity_k2_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.50  thf(l51_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X35 : $i, X36 : $i]:
% 0.22/0.50         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.22/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X35 : $i, X36 : $i]:
% 0.22/0.50         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.22/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain, (((k2_xboole_0 @ sk_D @ sk_C) = (sk_D))),
% 0.22/0.50      inference('demod', [status(thm)], ['21', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]:
% 0.22/0.50         ((k3_xboole_0 @ X11 @ X12)
% 0.22/0.50           = (k5_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ 
% 0.22/0.50              (k5_xboole_0 @ X11 @ X12)))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (((k3_xboole_0 @ sk_D @ sk_C)
% 0.22/0.50         = (k5_xboole_0 @ sk_D @ (k5_xboole_0 @ sk_D @ sk_C)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['13', '16'])).
% 0.22/0.50  thf('31', plain, (((k3_xboole_0 @ sk_D @ sk_C) = (sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (((k2_zfmisc_1 @ sk_A @ sk_C) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '1', '18', '31'])).
% 0.22/0.50  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
