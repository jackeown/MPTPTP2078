%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cWm55QOXPo

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:24 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 132 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  561 (1135 expanded)
%              Number of equality atoms :   41 (  67 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ X27 )
      | ( r1_tarski @ ( k1_setfam_1 @ X27 ) @ ( k1_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X15 @ X14 )
        = X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('24',plain,(
    ! [X15: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( ( k8_setfam_1 @ X15 @ k1_xboole_0 )
        = X15 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X15: $i] :
      ( ( k8_setfam_1 @ X15 @ k1_xboole_0 )
      = X15 ) ),
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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','35'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['36','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','44'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('46',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','54'])).

thf('56',plain,(
    ! [X15: $i] :
      ( ( k8_setfam_1 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('59',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55','56','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cWm55QOXPo
% 0.13/0.32  % Computer   : n001.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 16:58:00 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.32  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.18/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.58  % Solved by: fo/fo7.sh
% 0.18/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.58  % done 229 iterations in 0.149s
% 0.18/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.58  % SZS output start Refutation
% 0.18/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.18/0.58  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.18/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.18/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.18/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.58  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.18/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.18/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.18/0.58  thf(t59_setfam_1, conjecture,
% 0.18/0.58    (![A:$i,B:$i]:
% 0.18/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.58       ( ![C:$i]:
% 0.18/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.58           ( ( r1_tarski @ B @ C ) =>
% 0.18/0.58             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.18/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.58    (~( ![A:$i,B:$i]:
% 0.18/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.58          ( ![C:$i]:
% 0.18/0.58            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.58              ( ( r1_tarski @ B @ C ) =>
% 0.18/0.58                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.18/0.58    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.18/0.58  thf('0', plain,
% 0.18/0.58      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.18/0.58          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.18/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.58  thf('1', plain,
% 0.18/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.18/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.58  thf(d10_setfam_1, axiom,
% 0.18/0.58    (![A:$i,B:$i]:
% 0.18/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.58       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.18/0.58           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.18/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.18/0.58  thf('2', plain,
% 0.18/0.58      (![X14 : $i, X15 : $i]:
% 0.18/0.58         (((X14) = (k1_xboole_0))
% 0.18/0.58          | ((k8_setfam_1 @ X15 @ X14) = (k6_setfam_1 @ X15 @ X14))
% 0.18/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.18/0.58      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.18/0.58  thf('3', plain,
% 0.18/0.58      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.18/0.58        | ((sk_C_1) = (k1_xboole_0)))),
% 0.18/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.58  thf('4', plain,
% 0.18/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.18/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.58  thf(redefinition_k6_setfam_1, axiom,
% 0.18/0.58    (![A:$i,B:$i]:
% 0.18/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.58       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.18/0.58  thf('5', plain,
% 0.18/0.58      (![X18 : $i, X19 : $i]:
% 0.18/0.58         (((k6_setfam_1 @ X19 @ X18) = (k1_setfam_1 @ X18))
% 0.18/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.18/0.58      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.18/0.58  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.18/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.18/0.58  thf('7', plain,
% 0.18/0.58      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.18/0.58        | ((sk_C_1) = (k1_xboole_0)))),
% 0.18/0.58      inference('demod', [status(thm)], ['3', '6'])).
% 0.18/0.58  thf('8', plain,
% 0.18/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.18/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.58  thf('9', plain,
% 0.18/0.58      (![X14 : $i, X15 : $i]:
% 0.18/0.58         (((X14) = (k1_xboole_0))
% 0.18/0.58          | ((k8_setfam_1 @ X15 @ X14) = (k6_setfam_1 @ X15 @ X14))
% 0.18/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.18/0.58      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.18/0.58  thf('10', plain,
% 0.18/0.58      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.18/0.58        | ((sk_B_1) = (k1_xboole_0)))),
% 0.18/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.58  thf('11', plain,
% 0.18/0.58      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.18/0.58          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.18/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.58  thf('12', plain,
% 0.18/0.58      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.18/0.58           (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.18/0.58        | ((sk_B_1) = (k1_xboole_0)))),
% 0.18/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.18/0.58  thf('13', plain,
% 0.18/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.18/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.58  thf('14', plain,
% 0.18/0.58      (![X18 : $i, X19 : $i]:
% 0.18/0.58         (((k6_setfam_1 @ X19 @ X18) = (k1_setfam_1 @ X18))
% 0.18/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.18/0.58      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.18/0.58  thf('15', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.18/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.18/0.58  thf('16', plain,
% 0.18/0.58      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.18/0.58        | ((sk_B_1) = (k1_xboole_0)))),
% 0.18/0.58      inference('demod', [status(thm)], ['12', '15'])).
% 0.18/0.58  thf('17', plain,
% 0.18/0.58      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.18/0.58        | ((sk_C_1) = (k1_xboole_0))
% 0.18/0.58        | ((sk_B_1) = (k1_xboole_0)))),
% 0.18/0.58      inference('sup-', [status(thm)], ['7', '16'])).
% 0.18/0.58  thf('18', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.18/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.58  thf(t7_setfam_1, axiom,
% 0.18/0.58    (![A:$i,B:$i]:
% 0.18/0.58     ( ( r1_tarski @ A @ B ) =>
% 0.18/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.18/0.58         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.18/0.58  thf('19', plain,
% 0.18/0.58      (![X26 : $i, X27 : $i]:
% 0.18/0.58         (((X26) = (k1_xboole_0))
% 0.18/0.58          | ~ (r1_tarski @ X26 @ X27)
% 0.18/0.58          | (r1_tarski @ (k1_setfam_1 @ X27) @ (k1_setfam_1 @ X26)))),
% 0.18/0.58      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.18/0.58  thf('20', plain,
% 0.18/0.58      (((r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.18/0.58        | ((sk_B_1) = (k1_xboole_0)))),
% 0.18/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.18/0.58  thf('21', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.18/0.58      inference('clc', [status(thm)], ['17', '20'])).
% 0.18/0.58  thf(l13_xboole_0, axiom,
% 0.18/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.18/0.58  thf('22', plain,
% 0.18/0.58      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.18/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.18/0.58  thf('23', plain,
% 0.18/0.58      (![X14 : $i, X15 : $i]:
% 0.18/0.58         (((X14) != (k1_xboole_0))
% 0.18/0.58          | ((k8_setfam_1 @ X15 @ X14) = (X15))
% 0.18/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.18/0.58      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.18/0.58  thf('24', plain,
% 0.18/0.58      (![X15 : $i]:
% 0.18/0.58         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.18/0.58          | ((k8_setfam_1 @ X15 @ k1_xboole_0) = (X15)))),
% 0.18/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.18/0.58  thf(t4_subset_1, axiom,
% 0.18/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.18/0.58  thf('25', plain,
% 0.18/0.58      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.18/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.18/0.58  thf('26', plain, (![X15 : $i]: ((k8_setfam_1 @ X15 @ k1_xboole_0) = (X15))),
% 0.18/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.18/0.58  thf('27', plain,
% 0.18/0.58      (![X0 : $i, X1 : $i]:
% 0.18/0.58         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.18/0.58      inference('sup+', [status(thm)], ['22', '26'])).
% 0.18/0.58  thf('28', plain,
% 0.18/0.58      (![X0 : $i, X1 : $i]:
% 0.18/0.58         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.18/0.58      inference('sup+', [status(thm)], ['22', '26'])).
% 0.18/0.58  thf('29', plain,
% 0.18/0.58      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.18/0.58          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.18/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.58  thf('30', plain,
% 0.18/0.58      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.18/0.58        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.18/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.18/0.58  thf('31', plain,
% 0.18/0.58      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.18/0.58        | ~ (v1_xboole_0 @ sk_C_1)
% 0.18/0.58        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.18/0.58      inference('sup-', [status(thm)], ['27', '30'])).
% 0.18/0.58  thf(d3_tarski, axiom,
% 0.18/0.58    (![A:$i,B:$i]:
% 0.18/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.18/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.18/0.58  thf('32', plain,
% 0.18/0.58      (![X4 : $i, X6 : $i]:
% 0.18/0.58         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.18/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.18/0.58  thf('33', plain,
% 0.18/0.58      (![X4 : $i, X6 : $i]:
% 0.18/0.58         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.18/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.18/0.58  thf('34', plain,
% 0.18/0.58      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.18/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.18/0.58  thf('35', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.18/0.58      inference('simplify', [status(thm)], ['34'])).
% 0.18/0.58  thf('36', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.18/0.58      inference('demod', [status(thm)], ['31', '35'])).
% 0.18/0.58  thf(d1_xboole_0, axiom,
% 0.18/0.58    (![A:$i]:
% 0.18/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.18/0.58  thf('37', plain,
% 0.18/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.18/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.18/0.58  thf('38', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.18/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.58  thf('39', plain,
% 0.18/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.58         (~ (r2_hidden @ X3 @ X4)
% 0.18/0.58          | (r2_hidden @ X3 @ X5)
% 0.18/0.58          | ~ (r1_tarski @ X4 @ X5))),
% 0.18/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.18/0.58  thf('40', plain,
% 0.18/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.18/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.18/0.58  thf('41', plain,
% 0.18/0.58      (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_C_1))),
% 0.18/0.58      inference('sup-', [status(thm)], ['37', '40'])).
% 0.18/0.58  thf('42', plain,
% 0.18/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.18/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.18/0.58  thf('43', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.18/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.18/0.58  thf('44', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.18/0.58      inference('clc', [status(thm)], ['36', '43'])).
% 0.18/0.58  thf('45', plain,
% 0.18/0.58      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) = (k1_xboole_0)))),
% 0.18/0.58      inference('sup-', [status(thm)], ['21', '44'])).
% 0.18/0.58  thf(t4_boole, axiom,
% 0.18/0.58    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.18/0.58  thf('46', plain,
% 0.18/0.58      (![X8 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.18/0.58      inference('cnf', [status(esa)], [t4_boole])).
% 0.18/0.58  thf(t79_xboole_1, axiom,
% 0.18/0.58    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.18/0.58  thf('47', plain,
% 0.18/0.58      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 0.18/0.58      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.18/0.58  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.18/0.58      inference('sup+', [status(thm)], ['46', '47'])).
% 0.18/0.58  thf(t69_xboole_1, axiom,
% 0.18/0.58    (![A:$i,B:$i]:
% 0.18/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.18/0.58       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.18/0.58  thf('49', plain,
% 0.18/0.58      (![X9 : $i, X10 : $i]:
% 0.18/0.58         (~ (r1_xboole_0 @ X9 @ X10)
% 0.18/0.58          | ~ (r1_tarski @ X9 @ X10)
% 0.18/0.58          | (v1_xboole_0 @ X9))),
% 0.18/0.58      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.18/0.58  thf('50', plain,
% 0.18/0.58      (![X0 : $i]:
% 0.18/0.58         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.18/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.18/0.58  thf('51', plain,
% 0.18/0.58      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.18/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.18/0.58  thf(t3_subset, axiom,
% 0.18/0.58    (![A:$i,B:$i]:
% 0.18/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.58  thf('52', plain,
% 0.18/0.58      (![X20 : $i, X21 : $i]:
% 0.18/0.58         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.18/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.58  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.18/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.18/0.58  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.18/0.58      inference('demod', [status(thm)], ['50', '53'])).
% 0.18/0.58  thf('55', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.18/0.58      inference('demod', [status(thm)], ['45', '54'])).
% 0.18/0.58  thf('56', plain, (![X15 : $i]: ((k8_setfam_1 @ X15 @ k1_xboole_0) = (X15))),
% 0.18/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.18/0.58  thf('57', plain,
% 0.18/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.18/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.58  thf(dt_k8_setfam_1, axiom,
% 0.18/0.58    (![A:$i,B:$i]:
% 0.18/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.58       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.18/0.58  thf('58', plain,
% 0.18/0.58      (![X16 : $i, X17 : $i]:
% 0.18/0.58         ((m1_subset_1 @ (k8_setfam_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.18/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.18/0.58      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.18/0.58  thf('59', plain,
% 0.18/0.58      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.18/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.18/0.58  thf('60', plain,
% 0.18/0.58      (![X20 : $i, X21 : $i]:
% 0.18/0.58         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.18/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.58  thf('61', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.18/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.18/0.58  thf('62', plain, ($false),
% 0.18/0.58      inference('demod', [status(thm)], ['0', '55', '56', '61'])).
% 0.18/0.58  
% 0.18/0.58  % SZS output end Refutation
% 0.18/0.58  
% 0.18/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
