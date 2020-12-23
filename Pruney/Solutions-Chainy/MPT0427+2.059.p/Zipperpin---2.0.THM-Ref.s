%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.plArzPbKTr

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:28 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   68 (  87 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  463 ( 840 expanded)
%              Number of equality atoms :   45 (  54 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t59_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X11 @ X10 )
        = ( k6_setfam_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('3',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('6',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X11 @ X10 )
        = ( k6_setfam_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k6_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('15',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ X23 )
      | ( r1_tarski @ ( k1_setfam_1 @ X23 ) @ ( k1_setfam_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X3 )
      | ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('27',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k4_xboole_0 @ X6 @ X8 )
       != X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['25','29'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X11 @ X10 )
        = X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('35',plain,(
    ! [X11: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ( ( k8_setfam_1 @ X11 @ k1_xboole_0 )
        = X11 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k8_setfam_1 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('40',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33','37','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.plArzPbKTr
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:31:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 126 iterations in 0.056s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(t59_setfam_1, conjecture,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55       ( ![C:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55           ( ( r1_tarski @ B @ C ) =>
% 0.38/0.55             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i,B:$i]:
% 0.38/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55          ( ![C:$i]:
% 0.38/0.55            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55              ( ( r1_tarski @ B @ C ) =>
% 0.38/0.55                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(d10_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.55           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.38/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i]:
% 0.38/0.55         (((X10) = (k1_xboole_0))
% 0.38/0.55          | ((k8_setfam_1 @ X11 @ X10) = (k6_setfam_1 @ X11 @ X10))
% 0.38/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.38/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.38/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(redefinition_k6_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X14 : $i, X15 : $i]:
% 0.38/0.55         (((k6_setfam_1 @ X15 @ X14) = (k1_setfam_1 @ X14))
% 0.38/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.38/0.55  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.38/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.55      inference('demod', [status(thm)], ['3', '6'])).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i]:
% 0.38/0.55         (((X10) = (k1_xboole_0))
% 0.38/0.55          | ((k8_setfam_1 @ X11 @ X10) = (k6_setfam_1 @ X11 @ X10))
% 0.38/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.38/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.38/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      ((~ (r1_tarski @ (k6_setfam_1 @ sk_A @ sk_C) @ 
% 0.38/0.55           (k8_setfam_1 @ sk_A @ sk_B))
% 0.38/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X14 : $i, X15 : $i]:
% 0.38/0.55         (((k6_setfam_1 @ X15 @ X14) = (k1_setfam_1 @ X14))
% 0.38/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.38/0.55  thf('15', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.38/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))
% 0.38/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.55      inference('demod', [status(thm)], ['12', '15'])).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.38/0.55        | ((sk_B) = (k1_xboole_0))
% 0.38/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['7', '16'])).
% 0.38/0.55  thf('18', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t7_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.55         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (![X22 : $i, X23 : $i]:
% 0.38/0.55         (((X22) = (k1_xboole_0))
% 0.38/0.55          | ~ (r1_tarski @ X22 @ X23)
% 0.38/0.55          | (r1_tarski @ (k1_setfam_1 @ X23) @ (k1_setfam_1 @ X22)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.38/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.55  thf('21', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.55      inference('clc', [status(thm)], ['17', '20'])).
% 0.38/0.55  thf('22', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t63_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.38/0.55       ( r1_xboole_0 @ A @ C ) ))).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X1 @ X2)
% 0.38/0.55          | ~ (r1_xboole_0 @ X2 @ X3)
% 0.38/0.55          | (r1_xboole_0 @ X1 @ X3))),
% 0.38/0.55      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_C @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.55          | ((sk_B) = (k1_xboole_0))
% 0.38/0.55          | (r1_xboole_0 @ sk_B @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['21', '24'])).
% 0.38/0.55  thf(t4_boole, axiom,
% 0.38/0.55    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_boole])).
% 0.38/0.55  thf(t83_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X6 : $i, X8 : $i]:
% 0.38/0.55         ((r1_xboole_0 @ X6 @ X8) | ((k4_xboole_0 @ X6 @ X8) != (X6)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.55  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.38/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['25', '29'])).
% 0.38/0.55  thf(t66_xboole_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.38/0.55       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X5))),
% 0.38/0.55      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.38/0.55  thf('32', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.55  thf('33', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i]:
% 0.38/0.55         (((X10) != (k1_xboole_0))
% 0.38/0.55          | ((k8_setfam_1 @ X11 @ X10) = (X11))
% 0.38/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.38/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (![X11 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.38/0.55          | ((k8_setfam_1 @ X11 @ k1_xboole_0) = (X11)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.55  thf(t4_subset_1, axiom,
% 0.38/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.55  thf('37', plain, (![X11 : $i]: ((k8_setfam_1 @ X11 @ k1_xboole_0) = (X11))),
% 0.38/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(dt_k8_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      (![X12 : $i, X13 : $i]:
% 0.38/0.55         ((m1_subset_1 @ (k8_setfam_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.38/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.55  thf(t3_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i]:
% 0.38/0.55         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('42', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.55  thf('43', plain, ($false),
% 0.38/0.55      inference('demod', [status(thm)], ['0', '33', '37', '42'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
