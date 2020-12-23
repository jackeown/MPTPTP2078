%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0bNnwhVCsP

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:21 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 182 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  535 (1721 expanded)
%              Number of equality atoms :   50 ( 112 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ X26 )
      | ( r1_tarski @ ( k1_setfam_1 @ X26 ) @ ( k1_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('3',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X13 @ X12 )
        = ( k6_setfam_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('6',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k6_setfam_1 @ X17 @ X16 )
        = ( k1_setfam_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('9',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
    = ( k1_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X13 @ X12 )
        = ( k6_setfam_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('13',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k6_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k6_setfam_1 @ X17 @ X16 )
        = ( k1_setfam_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('18',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X5 )
        = X5 )
      | ~ ( r2_hidden @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','36'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X13 @ X12 )
        = X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('44',plain,(
    ! [X13: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( ( k8_setfam_1 @ X13 @ k1_xboole_0 )
        = X13 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k8_setfam_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
      = sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['37','38'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('49',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('52',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['40','49','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0bNnwhVCsP
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:54:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 157 iterations in 0.138s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.40/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.59  thf(t59_setfam_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.59       ( ![C:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.59           ( ( r1_tarski @ B @ C ) =>
% 0.40/0.59             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i]:
% 0.40/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.59          ( ![C:$i]:
% 0.40/0.59            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.59              ( ( r1_tarski @ B @ C ) =>
% 0.40/0.59                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.40/0.59          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('1', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t7_setfam_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r1_tarski @ A @ B ) =>
% 0.40/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.59         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X25 : $i, X26 : $i]:
% 0.40/0.59         (((X25) = (k1_xboole_0))
% 0.40/0.59          | ~ (r1_tarski @ X25 @ X26)
% 0.40/0.59          | (r1_tarski @ (k1_setfam_1 @ X26) @ (k1_setfam_1 @ X25)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.40/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d10_setfam_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.59       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.40/0.59           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.40/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X12 : $i, X13 : $i]:
% 0.40/0.59         (((X12) = (k1_xboole_0))
% 0.40/0.59          | ((k8_setfam_1 @ X13 @ X12) = (k6_setfam_1 @ X13 @ X12))
% 0.40/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.40/0.59      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.40/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k6_setfam_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.59       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (((k6_setfam_1 @ X17 @ X16) = (k1_setfam_1 @ X16))
% 0.40/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.40/0.59  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))
% 0.40/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['6', '9'])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X12 : $i, X13 : $i]:
% 0.40/0.59         (((X12) = (k1_xboole_0))
% 0.40/0.59          | ((k8_setfam_1 @ X13 @ X12) = (k6_setfam_1 @ X13 @ X12))
% 0.40/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.40/0.59      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.40/0.59        | ((sk_C) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.40/0.59          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      ((~ (r1_tarski @ (k6_setfam_1 @ sk_A @ sk_C) @ 
% 0.40/0.59           (k8_setfam_1 @ sk_A @ sk_B_1))
% 0.40/0.59        | ((sk_C) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (((k6_setfam_1 @ X17 @ X16) = (k1_setfam_1 @ X16))
% 0.40/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.40/0.59  thf('18', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B_1))
% 0.40/0.59        | ((sk_C) = (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['15', '18'])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.40/0.59        | ((sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_C) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['10', '19'])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      ((((sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | ((sk_C) = (k1_xboole_0))
% 0.40/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['3', '20'])).
% 0.40/0.59  thf('22', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['21'])).
% 0.40/0.59  thf('23', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t3_subset, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X22 : $i, X24 : $i]:
% 0.40/0.59         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('25', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.59  thf(cc1_subset_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.40/0.59          | (v1_xboole_0 @ X10)
% 0.40/0.59          | ~ (v1_xboole_0 @ X11))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.40/0.59  thf('27', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.59        | ((sk_B_1) = (k1_xboole_0))
% 0.40/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['22', '27'])).
% 0.40/0.59  thf(existence_m1_subset_1, axiom,
% 0.40/0.59    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.40/0.59  thf('29', plain, (![X9 : $i]: (m1_subset_1 @ (sk_B @ X9) @ X9)),
% 0.40/0.59      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.40/0.59  thf(t2_subset, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ A @ B ) =>
% 0.40/0.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (![X20 : $i, X21 : $i]:
% 0.40/0.59         ((r2_hidden @ X20 @ X21)
% 0.40/0.59          | (v1_xboole_0 @ X21)
% 0.40/0.59          | ~ (m1_subset_1 @ X20 @ X21))),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_subset])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.59  thf(l22_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r2_hidden @ A @ B ) =>
% 0.40/0.59       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (![X5 : $i, X6 : $i]:
% 0.40/0.59         (((k2_xboole_0 @ (k1_tarski @ X6) @ X5) = (X5))
% 0.40/0.59          | ~ (r2_hidden @ X6 @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ X0)
% 0.40/0.59          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.59  thf(t49_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i]:
% 0.40/0.59         ((k2_xboole_0 @ (k1_tarski @ X7) @ X8) != (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (v1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.59      inference('simplify', [status(thm)], ['35'])).
% 0.40/0.59  thf('37', plain, ((((sk_B_1) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_1))),
% 0.40/0.59      inference('demod', [status(thm)], ['28', '36'])).
% 0.40/0.59  thf(l13_xboole_0, axiom,
% 0.40/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.59  thf('39', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.40/0.59      inference('clc', [status(thm)], ['37', '38'])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.40/0.59          (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['0', '39'])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      (![X12 : $i, X13 : $i]:
% 0.40/0.59         (((X12) != (k1_xboole_0))
% 0.40/0.59          | ((k8_setfam_1 @ X13 @ X12) = (X13))
% 0.40/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.40/0.59      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (![X13 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.40/0.59          | ((k8_setfam_1 @ X13 @ k1_xboole_0) = (X13)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.40/0.59          | ~ (v1_xboole_0 @ X0)
% 0.40/0.59          | ((k8_setfam_1 @ X1 @ k1_xboole_0) = (X1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['42', '44'])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      ((((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))
% 0.40/0.59        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['41', '45'])).
% 0.40/0.59  thf('47', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.40/0.59      inference('clc', [status(thm)], ['37', '38'])).
% 0.40/0.59  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.59      inference('simplify', [status(thm)], ['35'])).
% 0.40/0.59  thf('49', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_k8_setfam_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.59       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]:
% 0.40/0.59         ((m1_subset_1 @ (k8_setfam_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.40/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i]:
% 0.40/0.59         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('54', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['52', '53'])).
% 0.40/0.59  thf('55', plain, ($false),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '49', '54'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
