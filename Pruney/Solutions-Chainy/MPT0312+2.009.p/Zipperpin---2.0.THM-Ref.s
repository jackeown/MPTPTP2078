%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yMXj80Thcy

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:13 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 136 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  440 (1067 expanded)
%              Number of equality atoms :   48 ( 112 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( sk_A
      = ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('26',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','25'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X13 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ X1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_C @ k1_xboole_0 ) )
    | ( sk_C
      = ( k3_xboole_0 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_C @ k1_xboole_0 ) )
    | ( sk_C
      = ( k4_xboole_0 @ sk_C @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('43',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_C )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','28','29','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yMXj80Thcy
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 249 iterations in 0.130s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.58  thf(t124_zfmisc_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.38/0.58       ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.38/0.58         ( k2_zfmisc_1 @ A @ C ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.38/0.58          ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.38/0.58            ( k2_zfmisc_1 @ A @ C ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t124_zfmisc_1])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 0.38/0.58         (k2_zfmisc_1 @ sk_B @ sk_C)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ 
% 0.38/0.58         (k2_zfmisc_1 @ sk_A @ sk_D)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.38/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.58  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(l32_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (![X5 : $i, X7 : $i]:
% 0.38/0.58         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.58  thf('5', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.58  thf(t48_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.38/0.58           = (k3_xboole_0 @ X11 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf(t17_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.38/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.38/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf(d10_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X2 : $i, X4 : $i]:
% 0.38/0.58         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.58          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      ((~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ k1_xboole_0))
% 0.38/0.58        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['10', '15'])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      ((~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ k1_xboole_0))
% 0.38/0.58        | ((sk_A) = (k4_xboole_0 @ sk_A @ k1_xboole_0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.38/0.58  thf(t2_boole, axiom,
% 0.38/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.38/0.58           = (k3_xboole_0 @ X11 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]:
% 0.38/0.58         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.38/0.58          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.58          | (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['19', '22'])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.58  thf('25', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['18', '24'])).
% 0.38/0.58  thf('26', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['9', '25'])).
% 0.38/0.58  thf(t123_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.38/0.58       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.58         ((k2_zfmisc_1 @ (k3_xboole_0 @ X13 @ X15) @ (k3_xboole_0 @ X14 @ X16))
% 0.38/0.58           = (k3_xboole_0 @ (k2_zfmisc_1 @ X13 @ X14) @ 
% 0.38/0.58              (k2_zfmisc_1 @ X15 @ X16)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.58           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ X1) @ 
% 0.38/0.58              (k2_zfmisc_1 @ sk_A @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['26', '27'])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('30', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (![X5 : $i, X7 : $i]:
% 0.38/0.58         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.58  thf('32', plain, (((k4_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.38/0.58           = (k3_xboole_0 @ X11 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.38/0.58      inference('sup+', [status(thm)], ['32', '33'])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_C))),
% 0.38/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_C))),
% 0.38/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.58          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.58  thf('39', plain,
% 0.38/0.58      ((~ (r1_tarski @ sk_C @ (k4_xboole_0 @ sk_C @ k1_xboole_0))
% 0.38/0.58        | ((sk_C) = (k3_xboole_0 @ sk_D @ sk_C)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_C))),
% 0.38/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      ((~ (r1_tarski @ sk_C @ (k4_xboole_0 @ sk_C @ k1_xboole_0))
% 0.38/0.58        | ((sk_C) = (k4_xboole_0 @ sk_C @ k1_xboole_0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.58  thf('43', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.58  thf('44', plain, (((sk_C) = (k3_xboole_0 @ sk_D @ sk_C))),
% 0.38/0.58      inference('demod', [status(thm)], ['36', '43'])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (((k2_zfmisc_1 @ sk_A @ sk_C) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.38/0.58      inference('demod', [status(thm)], ['2', '28', '29', '44'])).
% 0.38/0.58  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
