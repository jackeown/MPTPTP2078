%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.25oCemIPOu

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 145 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  462 (1504 expanded)
%              Number of equality atoms :   49 ( 106 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X10 @ X9 )
        = ( k6_setfam_1 @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( ( k6_setfam_1 @ X14 @ X13 )
        = ( k1_setfam_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X10 @ X9 )
        = ( k6_setfam_1 @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( ( k6_setfam_1 @ X14 @ X13 )
        = ( k1_setfam_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ ( k1_setfam_1 @ X21 ) @ ( k1_setfam_1 @ X20 ) ) ) ),
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

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('36',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X10 @ X9 )
        = X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('38',plain,(
    ! [X10: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( ( k8_setfam_1 @ X10 @ k1_xboole_0 )
        = X10 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('42',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['33','39','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.25oCemIPOu
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 111 iterations in 0.043s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(t59_setfam_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.49             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49          ( ![C:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49              ( ( r1_tarski @ B @ C ) =>
% 0.21/0.49                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d10_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (((X9) = (k1_xboole_0))
% 0.21/0.49          | ((k8_setfam_1 @ X10 @ X9) = (k6_setfam_1 @ X10 @ X9))
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k6_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (((k6_setfam_1 @ X14 @ X13) = (k1_setfam_1 @ X13))
% 0.21/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.49  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (((X9) = (k1_xboole_0))
% 0.21/0.49          | ((k8_setfam_1 @ X10 @ X9) = (k6_setfam_1 @ X10 @ X9))
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((~ (r1_tarski @ (k6_setfam_1 @ sk_A @ sk_C) @ 
% 0.21/0.49           (k8_setfam_1 @ sk_A @ sk_B))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (((k6_setfam_1 @ X14 @ X13) = (k1_setfam_1 @ X13))
% 0.21/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.49  thf('15', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '16'])).
% 0.21/0.49  thf('18', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t7_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i]:
% 0.21/0.49         (((X20) = (k1_xboole_0))
% 0.21/0.49          | ~ (r1_tarski @ X20 @ X21)
% 0.21/0.49          | (r1_tarski @ (k1_setfam_1 @ X21) @ (k1_setfam_1 @ X20)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('clc', [status(thm)], ['17', '20'])).
% 0.21/0.49  thf('22', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l32_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.49  thf('24', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['21', '24'])).
% 0.21/0.49  thf(t2_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.49  thf(t100_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.49           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf(t5_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.49  thf('29', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.49  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.49  thf('32', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.21/0.49          (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (((X9) != (k1_xboole_0))
% 0.21/0.49          | ((k8_setfam_1 @ X10 @ X9) = (X10))
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 0.21/0.49          | ((k8_setfam_1 @ X10 @ k1_xboole_0) = (X10)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.49  thf('39', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k8_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (k8_setfam_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]:
% 0.21/0.49         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('44', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain, ($false),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '39', '44'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
