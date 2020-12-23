%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2UELagj3E7

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:27 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 113 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  543 (1023 expanded)
%              Number of equality atoms :   50 (  68 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X14 @ X13 )
        = X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('5',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) )
      | ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
        = X14 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('7',plain,(
    ! [X14: $i] :
      ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X14 @ X13 )
        = ( k6_setfam_1 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('15',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k6_setfam_1 @ X18 @ X17 )
        = ( k1_setfam_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('18',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X14 @ X13 )
        = ( k6_setfam_1 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('22',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k6_setfam_1 @ X18 @ X17 )
        = ( k1_setfam_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('25',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ X26 )
      | ( r1_tarski @ ( k1_setfam_1 @ X26 ) @ ( k1_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('32',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['29','32'])).

thf('34',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 )
      | ( r1_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('43',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','48'])).

thf('50',plain,(
    k1_xboole_0 = sk_B ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X14: $i] :
      ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('52',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('55',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['52','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2UELagj3E7
% 0.16/0.37  % Computer   : n019.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:46:23 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.48  % Solved by: fo/fo7.sh
% 0.24/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.48  % done 153 iterations in 0.033s
% 0.24/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.48  % SZS output start Refutation
% 0.24/0.48  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.24/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.24/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.48  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.24/0.48  thf(t59_setfam_1, conjecture,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.48       ( ![C:$i]:
% 0.24/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.48           ( ( r1_tarski @ B @ C ) =>
% 0.24/0.48             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.24/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.48    (~( ![A:$i,B:$i]:
% 0.24/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.48          ( ![C:$i]:
% 0.24/0.48            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.48              ( ( r1_tarski @ B @ C ) =>
% 0.24/0.48                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.24/0.48    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.24/0.48  thf('0', plain,
% 0.24/0.48      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf(t4_subset_1, axiom,
% 0.24/0.48    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.48  thf('1', plain,
% 0.24/0.48      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.24/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.24/0.48  thf(dt_k8_setfam_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.48       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.48  thf('2', plain,
% 0.24/0.48      (![X15 : $i, X16 : $i]:
% 0.24/0.48         ((m1_subset_1 @ (k8_setfam_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.24/0.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.24/0.48      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.24/0.48  thf('3', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         (m1_subset_1 @ (k8_setfam_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.48  thf(d10_setfam_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.48       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.24/0.48           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.24/0.48         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.24/0.48  thf('4', plain,
% 0.24/0.48      (![X13 : $i, X14 : $i]:
% 0.24/0.48         (((X13) != (k1_xboole_0))
% 0.24/0.48          | ((k8_setfam_1 @ X14 @ X13) = (X14))
% 0.24/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.24/0.48      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.24/0.48  thf('5', plain,
% 0.24/0.48      (![X14 : $i]:
% 0.24/0.48         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14)))
% 0.24/0.48          | ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14)))),
% 0.24/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.24/0.48  thf('6', plain,
% 0.24/0.48      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.24/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.24/0.48  thf('7', plain, (![X14 : $i]: ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14))),
% 0.24/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.24/0.48  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.24/0.48      inference('demod', [status(thm)], ['3', '7'])).
% 0.24/0.48  thf(t3_subset, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.48  thf('9', plain,
% 0.24/0.48      (![X19 : $i, X20 : $i]:
% 0.24/0.48         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.48  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.24/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.48  thf(l32_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.48  thf('11', plain,
% 0.24/0.48      (![X0 : $i, X2 : $i]:
% 0.24/0.48         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.24/0.48  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.48  thf('13', plain,
% 0.24/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('14', plain,
% 0.24/0.48      (![X13 : $i, X14 : $i]:
% 0.24/0.48         (((X13) = (k1_xboole_0))
% 0.24/0.48          | ((k8_setfam_1 @ X14 @ X13) = (k6_setfam_1 @ X14 @ X13))
% 0.24/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.24/0.48      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.24/0.48  thf('15', plain,
% 0.24/0.48      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.24/0.48        | ((sk_C) = (k1_xboole_0)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.48  thf('16', plain,
% 0.24/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf(redefinition_k6_setfam_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.48       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.24/0.48  thf('17', plain,
% 0.24/0.48      (![X17 : $i, X18 : $i]:
% 0.24/0.48         (((k6_setfam_1 @ X18 @ X17) = (k1_setfam_1 @ X17))
% 0.24/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.24/0.48      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.24/0.48  thf('18', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.24/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.48  thf('19', plain,
% 0.24/0.48      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.24/0.48        | ((sk_C) = (k1_xboole_0)))),
% 0.24/0.48      inference('demod', [status(thm)], ['15', '18'])).
% 0.24/0.48  thf('20', plain,
% 0.24/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('21', plain,
% 0.24/0.48      (![X13 : $i, X14 : $i]:
% 0.24/0.48         (((X13) = (k1_xboole_0))
% 0.24/0.48          | ((k8_setfam_1 @ X14 @ X13) = (k6_setfam_1 @ X14 @ X13))
% 0.24/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.24/0.48      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.24/0.48  thf('22', plain,
% 0.24/0.48      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.24/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.48  thf('23', plain,
% 0.24/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('24', plain,
% 0.24/0.48      (![X17 : $i, X18 : $i]:
% 0.24/0.48         (((k6_setfam_1 @ X18 @ X17) = (k1_setfam_1 @ X17))
% 0.24/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.24/0.48      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.24/0.48  thf('25', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.24/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.24/0.48  thf('26', plain,
% 0.24/0.48      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.24/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.48      inference('demod', [status(thm)], ['22', '25'])).
% 0.24/0.48  thf('27', plain,
% 0.24/0.48      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('28', plain,
% 0.24/0.48      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.24/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.24/0.48  thf('29', plain,
% 0.24/0.48      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.24/0.48        | ((sk_C) = (k1_xboole_0))
% 0.24/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['19', '28'])).
% 0.24/0.48  thf('30', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf(t7_setfam_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.24/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.24/0.48         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.24/0.48  thf('31', plain,
% 0.24/0.48      (![X25 : $i, X26 : $i]:
% 0.24/0.48         (((X25) = (k1_xboole_0))
% 0.24/0.48          | ~ (r1_tarski @ X25 @ X26)
% 0.24/0.48          | (r1_tarski @ (k1_setfam_1 @ X26) @ (k1_setfam_1 @ X25)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.24/0.48  thf('32', plain,
% 0.24/0.48      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.24/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.24/0.48  thf('33', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.24/0.48      inference('clc', [status(thm)], ['29', '32'])).
% 0.24/0.48  thf('34', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf(t63_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i,C:$i]:
% 0.24/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.24/0.48       ( r1_xboole_0 @ A @ C ) ))).
% 0.24/0.48  thf('35', plain,
% 0.24/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.48         (~ (r1_tarski @ X6 @ X7)
% 0.24/0.48          | ~ (r1_xboole_0 @ X7 @ X8)
% 0.24/0.48          | (r1_xboole_0 @ X6 @ X8))),
% 0.24/0.48      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.24/0.48  thf('36', plain,
% 0.24/0.48      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_C @ X0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.48  thf('37', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.24/0.48          | ((sk_B) = (k1_xboole_0))
% 0.24/0.48          | (r1_xboole_0 @ sk_B @ X0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['33', '36'])).
% 0.24/0.48  thf('38', plain,
% 0.24/0.48      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.24/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.24/0.48  thf('39', plain,
% 0.24/0.48      (![X19 : $i, X20 : $i]:
% 0.24/0.48         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.48  thf('40', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.24/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.24/0.48  thf('41', plain,
% 0.24/0.48      (![X0 : $i, X2 : $i]:
% 0.24/0.48         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.24/0.48  thf('42', plain,
% 0.24/0.48      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.24/0.48  thf(t83_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.48  thf('43', plain,
% 0.24/0.48      (![X9 : $i, X11 : $i]:
% 0.24/0.48         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.24/0.48  thf('44', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.24/0.48  thf('45', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.24/0.48      inference('simplify', [status(thm)], ['44'])).
% 0.24/0.48  thf('46', plain,
% 0.24/0.48      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ X0))),
% 0.24/0.48      inference('demod', [status(thm)], ['37', '45'])).
% 0.24/0.48  thf('47', plain,
% 0.24/0.48      (![X9 : $i, X10 : $i]:
% 0.24/0.48         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.24/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.24/0.48  thf('48', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         (((sk_B) = (k1_xboole_0)) | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.24/0.48  thf('49', plain, ((((k1_xboole_0) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.48      inference('sup+', [status(thm)], ['12', '48'])).
% 0.24/0.48  thf('50', plain, (((k1_xboole_0) = (sk_B))),
% 0.24/0.48      inference('simplify', [status(thm)], ['49'])).
% 0.24/0.48  thf('51', plain, (![X14 : $i]: ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14))),
% 0.24/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.24/0.48  thf('52', plain, (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.24/0.48      inference('demod', [status(thm)], ['0', '50', '51'])).
% 0.24/0.48  thf('53', plain,
% 0.24/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('54', plain,
% 0.24/0.48      (![X15 : $i, X16 : $i]:
% 0.24/0.48         ((m1_subset_1 @ (k8_setfam_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.24/0.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.24/0.48      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.24/0.48  thf('55', plain,
% 0.24/0.48      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.24/0.48  thf('56', plain,
% 0.24/0.48      (![X19 : $i, X20 : $i]:
% 0.24/0.48         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.48  thf('57', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.24/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.24/0.48  thf('58', plain, ($false), inference('demod', [status(thm)], ['52', '57'])).
% 0.24/0.48  
% 0.24/0.48  % SZS output end Refutation
% 0.24/0.48  
% 0.24/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
