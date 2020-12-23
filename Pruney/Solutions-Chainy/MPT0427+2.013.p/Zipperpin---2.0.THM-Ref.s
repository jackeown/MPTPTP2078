%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kn7cJfWvwB

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 136 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  567 (1201 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ( r1_tarski @ ( k1_setfam_1 @ X22 ) @ ( k1_setfam_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('3',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X10 @ X9 )
        = ( k6_setfam_1 @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('6',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k6_setfam_1 @ X14 @ X13 )
        = ( k1_setfam_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('9',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X10 @ X9 )
        = ( k6_setfam_1 @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('13',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k6_setfam_1 @ X14 @ X13 )
        = ( k1_setfam_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('18',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X10 @ X9 )
        = X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('25',plain,(
    ! [X10: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( ( k8_setfam_1 @ X10 @ k1_xboole_0 )
        = X10 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k8_setfam_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','27'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference(clc,[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X10: $i] :
      ( ( k8_setfam_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X10: $i] :
      ( ( k8_setfam_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('61',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57','58','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kn7cJfWvwB
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:35:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.21/0.34  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 198 iterations in 0.098s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(t59_setfam_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.54             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i]:
% 0.21/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54          ( ![C:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54              ( ( r1_tarski @ B @ C ) =>
% 0.21/0.54                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t7_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i]:
% 0.21/0.54         (((X21) = (k1_xboole_0))
% 0.21/0.54          | ~ (r1_tarski @ X21 @ X22)
% 0.21/0.54          | (r1_tarski @ (k1_setfam_1 @ X22) @ (k1_setfam_1 @ X21)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d10_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.54           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.21/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         (((X9) = (k1_xboole_0))
% 0.21/0.54          | ((k8_setfam_1 @ X10 @ X9) = (k6_setfam_1 @ X10 @ X9))
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.21/0.54        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k6_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (((k6_setfam_1 @ X14 @ X13) = (k1_setfam_1 @ X13))
% 0.21/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.54  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.21/0.54        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '9'])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         (((X9) = (k1_xboole_0))
% 0.21/0.54          | ((k8_setfam_1 @ X10 @ X9) = (k6_setfam_1 @ X10 @ X9))
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.21/0.54           (k6_setfam_1 @ sk_A @ sk_B))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (((k6_setfam_1 @ X14 @ X13) = (k1_setfam_1 @ X13))
% 0.21/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.54  thf('18', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.21/0.54        | ((sk_C) = (k1_xboole_0))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      ((((sk_B) = (k1_xboole_0))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0))
% 0.21/0.54        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '20'])).
% 0.21/0.54  thf('22', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.54  thf(l13_xboole_0, axiom,
% 0.21/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         (((X9) != (k1_xboole_0))
% 0.21/0.54          | ((k8_setfam_1 @ X10 @ X9) = (X10))
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X10 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 0.21/0.54          | ((k8_setfam_1 @ X10 @ k1_xboole_0) = (X10)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.54  thf(t4_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf('27', plain, (![X10 : $i]: ((k8_setfam_1 @ X10 @ k1_xboole_0) = (X10))),
% 0.21/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['23', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['23', '27'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)
% 0.21/0.54        | ~ (v1_xboole_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.21/0.54        | ~ (v1_xboole_0 @ sk_C)
% 0.21/0.54        | ~ (v1_xboole_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '31'])).
% 0.21/0.54  thf('33', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X15 : $i, X17 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf(cc1_subset_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.21/0.54          | (v1_xboole_0 @ X7)
% 0.21/0.54          | ~ (v1_xboole_0 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.54  thf('37', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (r1_tarski @ sk_A @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['32', '37'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf(dt_k8_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k8_setfam_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (m1_subset_1 @ (k8_setfam_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.54  thf('42', plain, (![X10 : $i]: ((k8_setfam_1 @ X10 @ k1_xboole_0) = (X10))),
% 0.21/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('45', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('46', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '46'])).
% 0.21/0.54  thf(t4_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X1 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.54  thf(t79_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X5)),
% 0.21/0.54      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.54  thf('50', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.54      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf(t69_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.54       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (r1_xboole_0 @ X2 @ X3)
% 0.21/0.54          | ~ (r1_tarski @ X2 @ X3)
% 0.21/0.54          | (v1_xboole_0 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['52', '55'])).
% 0.21/0.54  thf('57', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['47', '56'])).
% 0.21/0.54  thf('58', plain, (![X10 : $i]: ((k8_setfam_1 @ X10 @ k1_xboole_0) = (X10))),
% 0.21/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k8_setfam_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('63', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.54  thf('64', plain, ($false),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '57', '58', '63'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
