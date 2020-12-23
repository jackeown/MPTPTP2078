%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fJQRcR3N5G

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:22 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 221 expanded)
%              Number of leaves         :   26 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  604 (1748 expanded)
%              Number of equality atoms :   47 ( 106 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X15 @ X14 )
        = ( k6_setfam_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('3',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k6_setfam_1 @ X19 @ X18 )
        = ( k1_setfam_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('6',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X15 @ X14 )
        = ( k6_setfam_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k6_setfam_1 @ X19 @ X18 )
        = ( k1_setfam_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('15',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
    = ( k1_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r1_tarski @ X23 @ X24 )
      | ( r1_tarski @ ( k1_setfam_1 @ X24 ) @ ( k1_setfam_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X10: $i] :
      ( ( r1_xboole_0 @ X10 @ X10 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('23',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('25',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','27'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('33',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X15 @ X14 )
        = X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('41',plain,(
    ! [X15: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( ( k8_setfam_1 @ X15 @ k1_xboole_0 )
        = X15 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k8_setfam_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','27'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k8_setfam_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','44'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['51','58'])).

thf('60',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','27'])).

thf('62',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k8_setfam_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('65',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('66',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62','63','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fJQRcR3N5G
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 214 iterations in 0.164s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.45/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(t59_setfam_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65       ( ![C:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65           ( ( r1_tarski @ B @ C ) =>
% 0.45/0.65             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i]:
% 0.45/0.65        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65          ( ![C:$i]:
% 0.45/0.65            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65              ( ( r1_tarski @ B @ C ) =>
% 0.45/0.65                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.45/0.65          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d10_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.45/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (((X14) = (k1_xboole_0))
% 0.45/0.65          | ((k8_setfam_1 @ X15 @ X14) = (k6_setfam_1 @ X15 @ X14))
% 0.45/0.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.45/0.65        | ((sk_C_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(redefinition_k6_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         (((k6_setfam_1 @ X19 @ X18) = (k1_setfam_1 @ X18))
% 0.45/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.45/0.65  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.45/0.65        | ((sk_C_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['3', '6'])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (((X14) = (k1_xboole_0))
% 0.45/0.65          | ((k8_setfam_1 @ X15 @ X14) = (k6_setfam_1 @ X15 @ X14))
% 0.45/0.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.45/0.65        | ((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.45/0.65          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.45/0.65           (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.45/0.65        | ((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         (((k6_setfam_1 @ X19 @ X18) = (k1_setfam_1 @ X18))
% 0.45/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.45/0.65  thf('15', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.45/0.65        | ((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['12', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.45/0.65        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.65        | ((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '16'])).
% 0.45/0.65  thf('18', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t7_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) =>
% 0.45/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.65         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         (((X23) = (k1_xboole_0))
% 0.45/0.65          | ~ (r1_tarski @ X23 @ X24)
% 0.45/0.65          | (r1_tarski @ (k1_setfam_1 @ X24) @ (k1_setfam_1 @ X23)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (((r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.45/0.65        | ((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.65  thf('21', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('clc', [status(thm)], ['17', '20'])).
% 0.45/0.65  thf(t66_xboole_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.45/0.65       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X10 : $i]: ((r1_xboole_0 @ X10 @ X10) | ((X10) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.45/0.65  thf('23', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.65  thf(t69_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.65       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i]:
% 0.45/0.65         (~ (r1_xboole_0 @ X12 @ X13)
% 0.45/0.65          | ~ (r1_tarski @ X12 @ X13)
% 0.45/0.65          | (v1_xboole_0 @ X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.65  thf(d10_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('27', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.45/0.65      inference('simplify', [status(thm)], ['26'])).
% 0.45/0.65  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '27'])).
% 0.45/0.65  thf(d3_tarski, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (![X4 : $i, X6 : $i]:
% 0.45/0.65         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.65  thf(d1_xboole_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X7 : $i, X9 : $i]:
% 0.45/0.65         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['31', '34'])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['28', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf(t3_subset, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X20 : $i, X22 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (((X14) != (k1_xboole_0))
% 0.45/0.65          | ((k8_setfam_1 @ X15 @ X14) = (X15))
% 0.45/0.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (![X15 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.45/0.65          | ((k8_setfam_1 @ X15 @ k1_xboole_0) = (X15)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['40'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.65          | ((k8_setfam_1 @ X0 @ k1_xboole_0) = (X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['39', '41'])).
% 0.45/0.65  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '27'])).
% 0.45/0.65  thf('44', plain, (![X0 : $i]: ((k8_setfam_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['36', '44'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['36', '44'])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.45/0.65          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.45/0.65        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.45/0.65        | ~ (v1_xboole_0 @ sk_C_1)
% 0.45/0.65        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['45', '48'])).
% 0.45/0.65  thf('50', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.45/0.65      inference('simplify', [status(thm)], ['26'])).
% 0.45/0.65  thf('51', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['49', '50'])).
% 0.45/0.65  thf('52', plain,
% 0.45/0.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf('53', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X3 @ X4)
% 0.45/0.65          | (r2_hidden @ X3 @ X5)
% 0.45/0.65          | ~ (r1_tarski @ X4 @ X5))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['52', '55'])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf('58', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('59', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.45/0.65      inference('clc', [status(thm)], ['51', '58'])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['21', '59'])).
% 0.45/0.65  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '27'])).
% 0.45/0.65  thf('62', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('63', plain, (![X0 : $i]: ((k8_setfam_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_k8_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((m1_subset_1 @ (k8_setfam_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.45/0.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (![X20 : $i, X21 : $i]:
% 0.45/0.65         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.65  thf('68', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.65  thf('69', plain, ($false),
% 0.45/0.65      inference('demod', [status(thm)], ['0', '62', '63', '68'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.48/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
