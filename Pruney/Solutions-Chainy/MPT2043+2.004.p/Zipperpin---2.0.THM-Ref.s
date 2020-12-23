%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mKeppprxJn

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 141 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  593 (1154 expanded)
%              Number of equality atoms :   42 (  74 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t2_yellow19,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
         => ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( v1_xboole_0 @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
           => ! [C: $i] :
                ~ ( ( r2_hidden @ C @ B )
                  & ( v1_xboole_0 @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_yellow19])).

thf('0',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    v1_subset_1 @ sk_B @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('6',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k9_setfam_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('15',plain,(
    ! [X14: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ( X5 = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ( X5 = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k9_setfam_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k9_setfam_1 @ sk_A ) ) @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k9_setfam_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B )
    | ( r1_tarski @ ( sk_C @ sk_B @ ( k9_setfam_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('25',plain,(
    v13_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t11_waybel_7,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) )
     => ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ D @ A )
              & ( r2_hidden @ C @ B ) )
           => ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ X20 ) )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ( r2_hidden @ X22 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X20 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_waybel_7])).

thf('27',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('28',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('30',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( v13_waybel_0 @ X19 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X20 ) ) )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ( r2_hidden @ X22 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k9_setfam_1 @ sk_A )
        = sk_B )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ ( k9_setfam_1 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ ( k9_setfam_1 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( k9_setfam_1 @ sk_A ) ) @ sk_B )
    | ~ ( r2_hidden @ k1_xboole_0 @ sk_B )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['10','35'])).

thf('37',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( k9_setfam_1 @ sk_A ) ) @ sk_B )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( X5 = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('44',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( X5 = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k9_setfam_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('48',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k9_setfam_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    v1_subset_1 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['3','49'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_subset_1 @ X18 @ X17 )
      | ( X18 != X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('52',plain,(
    ! [X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_subset_1 @ X17 @ X17 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('54',plain,(
    ! [X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k9_setfam_1 @ X17 ) )
      | ~ ( v1_subset_1 @ X17 @ X17 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('59',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k9_setfam_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X17: $i] :
      ~ ( v1_subset_1 @ X17 @ X17 ) ),
    inference(demod,[status(thm)],['54','60'])).

thf('62',plain,(
    $false ),
    inference('sup-',[status(thm)],['50','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mKeppprxJn
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 100 iterations in 0.059s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.52  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.52  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.52  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(t2_yellow19, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.20/0.52             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.52             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.52             ( m1_subset_1 @
% 0.20/0.52               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.20/0.52           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52                ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.20/0.52                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.52                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.52                ( m1_subset_1 @
% 0.20/0.52                  B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.20/0.52              ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t2_yellow19])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((v1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t4_yellow_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k2_yellow_1 @ (k9_setfam_1 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.52  thf(t1_yellow_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.52       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.52  thf('2', plain, (![X14 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X14)) = (X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('3', plain, ((v1_subset_1 @ sk_B @ (k9_setfam_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.20/0.52  thf(t4_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.52  thf(redefinition_k9_setfam_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.52  thf('5', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X6))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf(t3_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('8', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k9_setfam_1 @ X8)))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ 
% 0.20/0.52        (k9_setfam_1 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k2_yellow_1 @ (k9_setfam_1 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X14 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X14)) = (X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.52  thf(t49_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.52         ( ( A ) = ( B ) ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_C @ X4 @ X5) @ X5)
% 0.20/0.52          | ((X5) = (X4))
% 0.20/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.20/0.52  thf('18', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_C @ X4 @ X5) @ X5)
% 0.20/0.52          | ((X5) = (X4))
% 0.20/0.52          | ~ (m1_subset_1 @ X4 @ (k9_setfam_1 @ X5)))),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((((k9_setfam_1 @ sk_A) = (sk_B))
% 0.20/0.52        | (m1_subset_1 @ (sk_C @ sk_B @ (k9_setfam_1 @ sk_A)) @ 
% 0.20/0.52           (k9_setfam_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k9_setfam_1 @ X8)))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((((k9_setfam_1 @ sk_A) = (sk_B))
% 0.20/0.52        | (r1_tarski @ (sk_C @ sk_B @ (k9_setfam_1 @ sk_A)) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain, ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k2_yellow_1 @ (k9_setfam_1 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((v13_waybel_0 @ sk_B @ (k2_yellow_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf(t11_waybel_7, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @
% 0.20/0.52         B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) =>
% 0.20/0.52       ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) <=>
% 0.20/0.52         ( ![C:$i,D:$i]:
% 0.20/0.52           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ D @ A ) & 
% 0.20/0.52               ( r2_hidden @ C @ B ) ) =>
% 0.20/0.52             ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ X20))
% 0.20/0.52          | ~ (r2_hidden @ X21 @ X19)
% 0.20/0.52          | ~ (r1_tarski @ X21 @ X22)
% 0.20/0.52          | ~ (r1_tarski @ X22 @ X20)
% 0.20/0.52          | (r2_hidden @ X22 @ X19)
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ 
% 0.20/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X20)))))),
% 0.20/0.52      inference('cnf', [status(esa)], [t11_waybel_7])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k2_yellow_1 @ (k9_setfam_1 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k2_yellow_1 @ (k9_setfam_1 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X14 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X14)) = (X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('30', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (v13_waybel_0 @ X19 @ (k2_yellow_1 @ (k9_setfam_1 @ X20)))
% 0.20/0.52          | ~ (r2_hidden @ X21 @ X19)
% 0.20/0.52          | ~ (r1_tarski @ X21 @ X22)
% 0.20/0.52          | ~ (r1_tarski @ X22 @ X20)
% 0.20/0.52          | (r2_hidden @ X22 @ X19)
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ (k9_setfam_1 @ (k9_setfam_1 @ X20))))),
% 0.20/0.52      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ sk_B @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))
% 0.20/0.52          | (r2_hidden @ X0 @ sk_B)
% 0.20/0.52          | ~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X0)
% 0.20/0.52          | ~ (r2_hidden @ X1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ sk_B)
% 0.20/0.52          | ~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X0)
% 0.20/0.52          | ~ (r2_hidden @ X1 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k9_setfam_1 @ sk_A) = (sk_B))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.52          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ (k9_setfam_1 @ sk_A)))
% 0.20/0.52          | (r2_hidden @ (sk_C @ sk_B @ (k9_setfam_1 @ sk_A)) @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (((r2_hidden @ (sk_C @ sk_B @ (k9_setfam_1 @ sk_A)) @ sk_B)
% 0.20/0.52        | ~ (r2_hidden @ k1_xboole_0 @ sk_B)
% 0.20/0.52        | ((k9_setfam_1 @ sk_A) = (sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '35'])).
% 0.20/0.52  thf('37', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('38', plain, ((v1_xboole_0 @ sk_C_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(l13_xboole_0, axiom,
% 0.20/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.52  thf('40', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (((r2_hidden @ (sk_C @ sk_B @ (k9_setfam_1 @ sk_A)) @ sk_B)
% 0.20/0.52        | ((k9_setfam_1 @ sk_A) = (sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['36', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (sk_C @ X4 @ X5) @ X4)
% 0.20/0.52          | ((X5) = (X4))
% 0.20/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.20/0.52  thf('44', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (sk_C @ X4 @ X5) @ X4)
% 0.20/0.52          | ((X5) = (X4))
% 0.20/0.52          | ~ (m1_subset_1 @ X4 @ (k9_setfam_1 @ X5)))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((((k9_setfam_1 @ sk_A) = (sk_B))
% 0.20/0.52        | ~ (m1_subset_1 @ sk_B @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))
% 0.20/0.52        | ((k9_setfam_1 @ sk_A) = (sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((((k9_setfam_1 @ sk_A) = (sk_B)) | ((k9_setfam_1 @ sk_A) = (sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain, (((k9_setfam_1 @ sk_A) = (sk_B))),
% 0.20/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.52  thf('50', plain, ((v1_subset_1 @ sk_B @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '49'])).
% 0.20/0.52  thf(d7_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (v1_subset_1 @ X18 @ X17)
% 0.20/0.52          | ((X18) != (X17))
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X17 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X17))
% 0.20/0.52          | ~ (v1_subset_1 @ X17 @ X17))),
% 0.20/0.52      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.52  thf('53', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X17 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X17 @ (k9_setfam_1 @ X17))
% 0.20/0.52          | ~ (v1_subset_1 @ X17 @ X17))),
% 0.20/0.52      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('56', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.52      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X7 : $i, X9 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('58', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X7 : $i, X9 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X7 @ (k9_setfam_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.52  thf('60', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k9_setfam_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['56', '59'])).
% 0.20/0.52  thf('61', plain, (![X17 : $i]: ~ (v1_subset_1 @ X17 @ X17)),
% 0.20/0.52      inference('demod', [status(thm)], ['54', '60'])).
% 0.20/0.52  thf('62', plain, ($false), inference('sup-', [status(thm)], ['50', '61'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
