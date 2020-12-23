%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X8Iq0lm9Pb

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 (  71 expanded)
%              Number of leaves         :   29 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  410 ( 535 expanded)
%              Number of equality atoms :   41 (  54 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t11_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
            = ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k5_setfam_1 @ A @ B ) )
          = ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( ( k7_subset_1 @ X25 @ ( k2_subset_1 @ X25 ) @ ( k5_setfam_1 @ X25 @ X24 ) )
        = ( k6_setfam_1 @ X25 @ ( k7_setfam_1 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t47_setfam_1])).

thf('2',plain,
    ( ( ( k7_subset_1 @ sk_A @ ( k2_subset_1 @ sk_A ) @ ( k5_setfam_1 @ sk_A @ sk_B ) )
      = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k7_subset_1 @ sk_A @ ( k2_subset_1 @ sk_A ) @ ( k5_setfam_1 @ sk_A @ sk_B ) )
    = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k1_subset_1 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = ( k3_subset_1 @ X15 @ ( k1_subset_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k7_subset_1 @ sk_A @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) )
    = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) )
    = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('26',plain,(
    ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('29',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('31',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X8Iq0lm9Pb
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:08:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 239 iterations in 0.092s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.22/0.55  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.22/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(t11_tops_2, conjecture,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.55       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.55         ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.22/0.55           ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i]:
% 0.22/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.55          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.55            ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.22/0.55              ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t11_tops_2])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t47_setfam_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.55       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.55         ( ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k5_setfam_1 @ A @ B ) ) =
% 0.22/0.55           ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) ) ) ))).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (![X24 : $i, X25 : $i]:
% 0.22/0.55         (((X24) = (k1_xboole_0))
% 0.22/0.55          | ((k7_subset_1 @ X25 @ (k2_subset_1 @ X25) @ 
% 0.22/0.55              (k5_setfam_1 @ X25 @ X24))
% 0.22/0.55              = (k6_setfam_1 @ X25 @ (k7_setfam_1 @ X25 @ X24)))
% 0.22/0.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 0.22/0.55      inference('cnf', [status(esa)], [t47_setfam_1])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      ((((k7_subset_1 @ sk_A @ (k2_subset_1 @ sk_A) @ 
% 0.22/0.55          (k5_setfam_1 @ sk_A @ sk_B))
% 0.22/0.55          = (k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.55  thf('3', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (((k7_subset_1 @ sk_A @ (k2_subset_1 @ sk_A) @ 
% 0.22/0.55         (k5_setfam_1 @ sk_A @ sk_B))
% 0.22/0.55         = (k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf(t4_subset_1, axiom,
% 0.22/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf(d5_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X10 : $i, X11 : $i]:
% 0.22/0.55         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.22/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf(t2_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.55  thf(t100_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X3 @ X4)
% 0.22/0.55           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf(t5_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.55  thf('11', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.22/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.55  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['7', '12'])).
% 0.22/0.55  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.55  thf('14', plain, (![X9 : $i]: ((k1_subset_1 @ X9) = (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.55  thf(t22_subset_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X15 : $i]:
% 0.22/0.55         ((k2_subset_1 @ X15) = (k3_subset_1 @ X15 @ (k1_subset_1 @ X15)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X0 : $i]: ((k2_subset_1 @ X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.55  thf('17', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['13', '16'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (((k7_subset_1 @ sk_A @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B))
% 0.22/0.55         = (k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['4', '17'])).
% 0.22/0.55  thf(d10_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.56  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.56  thf(t3_subset, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (![X21 : $i, X23 : $i]:
% 0.22/0.56         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.22/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.56  thf('22', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.56  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.56       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.56  thf('23', plain,
% 0.22/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.22/0.56          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      (((k4_xboole_0 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B))
% 0.22/0.56         = (k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.56      inference('demod', [status(thm)], ['18', '24'])).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      (((k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.22/0.56         != (k3_subset_1 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('27', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(dt_k5_setfam_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.56       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (![X17 : $i, X18 : $i]:
% 0.22/0.56         ((m1_subset_1 @ (k5_setfam_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.22/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.56  thf('30', plain,
% 0.22/0.56      (![X10 : $i, X11 : $i]:
% 0.22/0.56         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.22/0.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.56  thf('31', plain,
% 0.22/0.56      (((k3_subset_1 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B))
% 0.22/0.56         = (k4_xboole_0 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.56  thf('32', plain,
% 0.22/0.56      (((k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.22/0.56         != (k4_xboole_0 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.56      inference('demod', [status(thm)], ['26', '31'])).
% 0.22/0.56  thf('33', plain, ($false),
% 0.22/0.56      inference('simplify_reflect-', [status(thm)], ['25', '32'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
