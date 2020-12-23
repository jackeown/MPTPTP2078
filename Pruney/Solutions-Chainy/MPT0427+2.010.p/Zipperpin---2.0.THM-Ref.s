%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k1FwTrxP32

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:21 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 141 expanded)
%              Number of leaves         :   25 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  562 (1235 expanded)
%              Number of equality atoms :   43 (  77 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X14 @ X13 )
        = ( k6_setfam_1 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('3',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k6_setfam_1 @ X18 @ X17 )
        = ( k1_setfam_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('6',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X14 @ X13 )
        = ( k6_setfam_1 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k6_setfam_1 @ X18 @ X17 )
        = ( k1_setfam_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('13',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ X26 )
      | ( r1_tarski @ ( k1_setfam_1 @ X26 ) @ ( k1_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X14 @ X13 )
        = X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('24',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) )
      | ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
        = X14 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X14: $i] :
      ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference(clc,[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X14: $i] :
      ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','45'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','55'])).

thf('57',plain,(
    ! [X14: $i] :
      ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('60',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56','57','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k1FwTrxP32
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 272 iterations in 0.168s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.42/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(t59_setfam_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62           ( ( r1_tarski @ B @ C ) =>
% 0.42/0.62             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62          ( ![C:$i]:
% 0.42/0.62            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62              ( ( r1_tarski @ B @ C ) =>
% 0.42/0.62                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(d10_setfam_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.42/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X13 : $i, X14 : $i]:
% 0.42/0.62         (((X13) = (k1_xboole_0))
% 0.42/0.62          | ((k8_setfam_1 @ X14 @ X13) = (k6_setfam_1 @ X14 @ X13))
% 0.42/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.42/0.62      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.42/0.62        | ((sk_C) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(redefinition_k6_setfam_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X17 : $i, X18 : $i]:
% 0.42/0.62         (((k6_setfam_1 @ X18 @ X17) = (k1_setfam_1 @ X17))
% 0.42/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.42/0.62  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.42/0.62        | ((sk_C) = (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['3', '6'])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X13 : $i, X14 : $i]:
% 0.42/0.62         (((X13) = (k1_xboole_0))
% 0.42/0.62          | ((k8_setfam_1 @ X14 @ X13) = (k6_setfam_1 @ X14 @ X13))
% 0.42/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.42/0.62      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.42/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X17 : $i, X18 : $i]:
% 0.42/0.62         (((k6_setfam_1 @ X18 @ X17) = (k1_setfam_1 @ X17))
% 0.42/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.42/0.62  thf('13', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.42/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['10', '13'])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.42/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.42/0.62        | ((sk_C) = (k1_xboole_0))
% 0.42/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['7', '16'])).
% 0.42/0.62  thf('18', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t7_setfam_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) =>
% 0.42/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X25 : $i, X26 : $i]:
% 0.42/0.62         (((X25) = (k1_xboole_0))
% 0.42/0.62          | ~ (r1_tarski @ X25 @ X26)
% 0.42/0.62          | (r1_tarski @ (k1_setfam_1 @ X26) @ (k1_setfam_1 @ X25)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.42/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.62  thf('21', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.42/0.62      inference('clc', [status(thm)], ['17', '20'])).
% 0.42/0.62  thf(l13_xboole_0, axiom,
% 0.42/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X13 : $i, X14 : $i]:
% 0.42/0.62         (((X13) != (k1_xboole_0))
% 0.42/0.62          | ((k8_setfam_1 @ X14 @ X13) = (X14))
% 0.42/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.42/0.62      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14)))
% 0.42/0.62          | ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['23'])).
% 0.42/0.62  thf(t4_subset_1, axiom,
% 0.42/0.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.42/0.62  thf('26', plain, (![X14 : $i]: ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14))),
% 0.42/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['22', '26'])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['22', '26'])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)
% 0.42/0.62        | ~ (v1_xboole_0 @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.42/0.62        | ~ (v1_xboole_0 @ sk_C)
% 0.42/0.62        | ~ (v1_xboole_0 @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['27', '30'])).
% 0.42/0.62  thf('32', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t3_subset, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (![X19 : $i, X21 : $i]:
% 0.42/0.62         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.62  thf('34', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.62  thf(cc1_subset_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_xboole_0 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X11 : $i, X12 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.42/0.62          | (v1_xboole_0 @ X11)
% 0.42/0.62          | ~ (v1_xboole_0 @ X12))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.42/0.62  thf('36', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.42/0.62  thf('37', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (r1_tarski @ sk_A @ sk_A))),
% 0.42/0.62      inference('clc', [status(thm)], ['31', '36'])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.42/0.62  thf(dt_k8_setfam_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]:
% 0.42/0.62         ((m1_subset_1 @ (k8_setfam_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.42/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.42/0.62  thf('40', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (m1_subset_1 @ (k8_setfam_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.42/0.62  thf('41', plain, (![X14 : $i]: ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14))),
% 0.42/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.42/0.62  thf('42', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (![X19 : $i, X20 : $i]:
% 0.42/0.62         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.62  thf('44', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.42/0.62  thf('45', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['37', '44'])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['21', '45'])).
% 0.42/0.62  thf(t36_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.42/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.42/0.62  thf(t79_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (![X8 : $i, X9 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X9)),
% 0.42/0.62      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.42/0.62  thf(t69_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.62       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i]:
% 0.42/0.62         (~ (r1_xboole_0 @ X6 @ X7)
% 0.42/0.62          | ~ (r1_tarski @ X6 @ X7)
% 0.42/0.62          | (v1_xboole_0 @ X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.42/0.62  thf('50', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.42/0.62          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.42/0.62  thf('51', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['47', '50'])).
% 0.42/0.62  thf('52', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['47', '50'])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.62  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.42/0.62  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('demod', [status(thm)], ['51', '54'])).
% 0.42/0.62  thf('56', plain, (((sk_B) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['46', '55'])).
% 0.42/0.62  thf('57', plain, (![X14 : $i]: ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14))),
% 0.42/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.42/0.62  thf('58', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('59', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]:
% 0.42/0.62         ((m1_subset_1 @ (k8_setfam_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.42/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.42/0.62  thf('60', plain,
% 0.42/0.62      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.42/0.62  thf('61', plain,
% 0.42/0.62      (![X19 : $i, X20 : $i]:
% 0.42/0.62         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.62  thf('62', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.62  thf('63', plain, ($false),
% 0.42/0.62      inference('demod', [status(thm)], ['0', '56', '57', '62'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
