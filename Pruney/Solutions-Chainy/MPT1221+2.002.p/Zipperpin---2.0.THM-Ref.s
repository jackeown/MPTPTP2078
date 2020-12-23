%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5mt0fIelS4

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:42 EST 2020

% Result     : Theorem 5.12s
% Output     : Refutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :  227 (1436 expanded)
%              Number of leaves         :   39 ( 455 expanded)
%              Depth                    :   25
%              Number of atoms          : 2032 (14991 expanded)
%              Number of equality atoms :  131 (1082 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('23',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('25',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('29',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('32',plain,(
    ! [X36: $i] :
      ( ( l1_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','48'])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('53',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup+',[status(thm)],['24','53'])).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('56',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X19 ) @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('57',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('58',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('62',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','70'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('72',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X27 @ X25 )
        = ( k9_subset_1 @ X26 @ X27 @ ( k3_subset_1 @ X26 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('76',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('80',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('85',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('86',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('87',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['73','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      = ( k9_subset_1 @ X0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','94'])).

thf('96',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('97',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('98',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('99',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['97','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['96','107'])).

thf('109',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('112',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('113',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('114',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('115',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X1 @ X0 @ X1 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k9_subset_1 @ X0 @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k9_subset_1 @ X1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','127'])).

thf('129',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k9_subset_1 @ X1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['95','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','132'])).

thf('134',plain,
    ( ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['54','133'])).

thf('135',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup+',[status(thm)],['24','53'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('137',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('140',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['140'])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('143',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v4_pre_topc @ X34 @ X35 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k2_struct_0 @ X35 ) @ X34 ) @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('144',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,
    ( ( ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['139','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('150',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['138','150'])).

thf('152',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('153',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('155',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('157',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('158',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['155','158'])).

thf('160',plain,
    ( ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['152','159'])).

thf('161',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('162',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['151','162'])).

thf('164',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['140'])).

thf('165',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('166',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('167',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('168',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['140'])).

thf('169',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['166','169'])).

thf('171',plain,
    ( ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['165','170'])).

thf('172',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('173',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['134','137'])).

thf('175',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('176',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k2_struct_0 @ X35 ) @ X34 ) @ X35 )
      | ( v4_pre_topc @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['174','177'])).

thf('179',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('182',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['178','179','180','181'])).

thf('183',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['173','182'])).

thf('184',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('185',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','163','164','185'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5mt0fIelS4
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:18:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 5.12/5.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.12/5.32  % Solved by: fo/fo7.sh
% 5.12/5.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.12/5.32  % done 3860 iterations in 4.836s
% 5.12/5.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.12/5.32  % SZS output start Refutation
% 5.12/5.32  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 5.12/5.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.12/5.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.12/5.32  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.12/5.32  thf(sk_B_type, type, sk_B: $i).
% 5.12/5.32  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.12/5.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.12/5.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.12/5.32  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.12/5.32  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.12/5.32  thf(sk_A_type, type, sk_A: $i).
% 5.12/5.32  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.12/5.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.12/5.32  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.12/5.32  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.12/5.32  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.12/5.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.12/5.32  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 5.12/5.32  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.12/5.32  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 5.12/5.32  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.12/5.32  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.12/5.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.12/5.32  thf(t29_tops_1, conjecture,
% 5.12/5.32    (![A:$i]:
% 5.12/5.32     ( ( l1_pre_topc @ A ) =>
% 5.12/5.32       ( ![B:$i]:
% 5.12/5.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.12/5.32           ( ( v4_pre_topc @ B @ A ) <=>
% 5.12/5.32             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 5.12/5.32  thf(zf_stmt_0, negated_conjecture,
% 5.12/5.32    (~( ![A:$i]:
% 5.12/5.32        ( ( l1_pre_topc @ A ) =>
% 5.12/5.32          ( ![B:$i]:
% 5.12/5.32            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.12/5.32              ( ( v4_pre_topc @ B @ A ) <=>
% 5.12/5.32                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 5.12/5.32    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 5.12/5.32  thf('0', plain,
% 5.12/5.32      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.12/5.32        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.12/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.12/5.32  thf('1', plain,
% 5.12/5.32      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 5.12/5.32       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.12/5.32      inference('split', [status(esa)], ['0'])).
% 5.12/5.32  thf(d4_xboole_0, axiom,
% 5.12/5.32    (![A:$i,B:$i,C:$i]:
% 5.12/5.32     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 5.12/5.32       ( ![D:$i]:
% 5.12/5.32         ( ( r2_hidden @ D @ C ) <=>
% 5.12/5.32           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.12/5.32  thf('2', plain,
% 5.12/5.32      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.12/5.32         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 5.12/5.32          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 5.12/5.32          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.12/5.32      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.12/5.32  thf(t12_setfam_1, axiom,
% 5.12/5.32    (![A:$i,B:$i]:
% 5.12/5.32     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.12/5.32  thf('3', plain,
% 5.12/5.32      (![X28 : $i, X29 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 5.12/5.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.12/5.32  thf('4', plain,
% 5.12/5.32      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.12/5.32         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 5.12/5.32          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 5.12/5.32          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.12/5.32      inference('demod', [status(thm)], ['2', '3'])).
% 5.12/5.32  thf('5', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.12/5.32          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('eq_fact', [status(thm)], ['4'])).
% 5.12/5.32  thf('6', plain,
% 5.12/5.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.12/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.12/5.32  thf(t3_subset, axiom,
% 5.12/5.32    (![A:$i,B:$i]:
% 5.12/5.32     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.12/5.32  thf('7', plain,
% 5.12/5.32      (![X30 : $i, X31 : $i]:
% 5.12/5.32         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 5.12/5.32      inference('cnf', [status(esa)], [t3_subset])).
% 5.12/5.32  thf('8', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.12/5.32      inference('sup-', [status(thm)], ['6', '7'])).
% 5.12/5.32  thf(d3_tarski, axiom,
% 5.12/5.32    (![A:$i,B:$i]:
% 5.12/5.32     ( ( r1_tarski @ A @ B ) <=>
% 5.12/5.32       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.12/5.32  thf('9', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.12/5.32         (~ (r2_hidden @ X0 @ X1)
% 5.12/5.32          | (r2_hidden @ X0 @ X2)
% 5.12/5.32          | ~ (r1_tarski @ X1 @ X2))),
% 5.12/5.32      inference('cnf', [status(esa)], [d3_tarski])).
% 5.12/5.32  thf('10', plain,
% 5.12/5.32      (![X0 : $i]:
% 5.12/5.32         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 5.12/5.32      inference('sup-', [status(thm)], ['8', '9'])).
% 5.12/5.32  thf('11', plain,
% 5.12/5.32      (![X0 : $i]:
% 5.12/5.32         (((sk_B) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)))
% 5.12/5.32          | (r2_hidden @ (sk_D @ sk_B @ sk_B @ X0) @ (u1_struct_0 @ sk_A)))),
% 5.12/5.32      inference('sup-', [status(thm)], ['5', '10'])).
% 5.12/5.32  thf('12', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.12/5.32          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('eq_fact', [status(thm)], ['4'])).
% 5.12/5.32  thf('13', plain,
% 5.12/5.32      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.12/5.32         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.12/5.32      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.12/5.32  thf('14', plain,
% 5.12/5.32      (![X28 : $i, X29 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 5.12/5.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.12/5.32  thf('15', plain,
% 5.12/5.32      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.12/5.32         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.12/5.32      inference('demod', [status(thm)], ['13', '14'])).
% 5.12/5.32  thf('16', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 5.12/5.32          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('sup-', [status(thm)], ['12', '15'])).
% 5.12/5.32  thf('17', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.12/5.32          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('simplify', [status(thm)], ['16'])).
% 5.12/5.32  thf('18', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.12/5.32          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('eq_fact', [status(thm)], ['4'])).
% 5.12/5.32  thf('19', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 5.12/5.32      inference('clc', [status(thm)], ['17', '18'])).
% 5.12/5.32  thf('20', plain,
% 5.12/5.32      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B)))
% 5.12/5.32        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 5.12/5.32      inference('sup-', [status(thm)], ['11', '19'])).
% 5.12/5.32  thf(commutativity_k2_tarski, axiom,
% 5.12/5.32    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 5.12/5.32  thf('21', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf('22', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf('23', plain,
% 5.12/5.32      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))
% 5.12/5.32        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A)))))),
% 5.12/5.32      inference('demod', [status(thm)], ['20', '21', '22'])).
% 5.12/5.32  thf('24', plain,
% 5.12/5.32      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 5.12/5.32      inference('simplify', [status(thm)], ['23'])).
% 5.12/5.32  thf(d3_struct_0, axiom,
% 5.12/5.32    (![A:$i]:
% 5.12/5.32     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.12/5.32  thf('25', plain,
% 5.12/5.32      (![X33 : $i]:
% 5.12/5.32         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 5.12/5.32      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.12/5.32  thf('26', plain,
% 5.12/5.32      (![X33 : $i]:
% 5.12/5.32         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 5.12/5.32      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.12/5.32  thf('27', plain,
% 5.12/5.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.12/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.12/5.32  thf(d5_subset_1, axiom,
% 5.12/5.32    (![A:$i,B:$i]:
% 5.12/5.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.12/5.32       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.12/5.32  thf('28', plain,
% 5.12/5.32      (![X17 : $i, X18 : $i]:
% 5.12/5.32         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 5.12/5.32          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 5.12/5.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.12/5.32  thf('29', plain,
% 5.12/5.32      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('sup-', [status(thm)], ['27', '28'])).
% 5.12/5.32  thf('30', plain,
% 5.12/5.32      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 5.12/5.32        | ~ (l1_struct_0 @ sk_A))),
% 5.12/5.32      inference('sup+', [status(thm)], ['26', '29'])).
% 5.12/5.32  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 5.12/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.12/5.32  thf(dt_l1_pre_topc, axiom,
% 5.12/5.32    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 5.12/5.32  thf('32', plain,
% 5.12/5.32      (![X36 : $i]: ((l1_struct_0 @ X36) | ~ (l1_pre_topc @ X36))),
% 5.12/5.32      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.12/5.32  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 5.12/5.32      inference('sup-', [status(thm)], ['31', '32'])).
% 5.12/5.32  thf('34', plain,
% 5.12/5.32      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('demod', [status(thm)], ['30', '33'])).
% 5.12/5.32  thf('35', plain,
% 5.12/5.32      (![X33 : $i]:
% 5.12/5.32         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 5.12/5.32      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.12/5.32  thf('36', plain,
% 5.12/5.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.12/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.12/5.32  thf('37', plain,
% 5.12/5.32      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.12/5.32        | ~ (l1_struct_0 @ sk_A))),
% 5.12/5.32      inference('sup+', [status(thm)], ['35', '36'])).
% 5.12/5.32  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 5.12/5.32      inference('sup-', [status(thm)], ['31', '32'])).
% 5.12/5.32  thf('39', plain,
% 5.12/5.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 5.12/5.32      inference('demod', [status(thm)], ['37', '38'])).
% 5.12/5.32  thf('40', plain,
% 5.12/5.32      (![X17 : $i, X18 : $i]:
% 5.12/5.32         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 5.12/5.32          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 5.12/5.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.12/5.32  thf('41', plain,
% 5.12/5.32      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('sup-', [status(thm)], ['39', '40'])).
% 5.12/5.32  thf('42', plain,
% 5.12/5.32      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('sup+', [status(thm)], ['34', '41'])).
% 5.12/5.32  thf(t48_xboole_1, axiom,
% 5.12/5.32    (![A:$i,B:$i]:
% 5.12/5.32     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.12/5.32  thf('43', plain,
% 5.12/5.32      (![X12 : $i, X13 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 5.12/5.32           = (k3_xboole_0 @ X12 @ X13))),
% 5.12/5.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.12/5.32  thf('44', plain,
% 5.12/5.32      (![X28 : $i, X29 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 5.12/5.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.12/5.32  thf('45', plain,
% 5.12/5.32      (![X12 : $i, X13 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 5.12/5.32           = (k1_setfam_1 @ (k2_tarski @ X12 @ X13)))),
% 5.12/5.32      inference('demod', [status(thm)], ['43', '44'])).
% 5.12/5.32  thf('46', plain,
% 5.12/5.32      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.12/5.32         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.12/5.32         = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 5.12/5.32      inference('sup+', [status(thm)], ['42', '45'])).
% 5.12/5.32  thf('47', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf('48', plain,
% 5.12/5.32      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.12/5.32         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.12/5.32         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 5.12/5.32      inference('demod', [status(thm)], ['46', '47'])).
% 5.12/5.32  thf('49', plain,
% 5.12/5.32      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 5.12/5.32          (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.12/5.32          = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))
% 5.12/5.32        | ~ (l1_struct_0 @ sk_A))),
% 5.12/5.32      inference('sup+', [status(thm)], ['25', '48'])).
% 5.12/5.32  thf('50', plain,
% 5.12/5.32      (![X12 : $i, X13 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 5.12/5.32           = (k1_setfam_1 @ (k2_tarski @ X12 @ X13)))),
% 5.12/5.32      inference('demod', [status(thm)], ['43', '44'])).
% 5.12/5.32  thf('51', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 5.12/5.32      inference('sup-', [status(thm)], ['31', '32'])).
% 5.12/5.32  thf('53', plain,
% 5.12/5.32      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A)))
% 5.12/5.32         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 5.12/5.32      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 5.12/5.32  thf('54', plain,
% 5.12/5.32      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A))) = (sk_B))),
% 5.12/5.32      inference('sup+', [status(thm)], ['24', '53'])).
% 5.12/5.32  thf('55', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf(dt_k2_subset_1, axiom,
% 5.12/5.32    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.12/5.32  thf('56', plain,
% 5.12/5.32      (![X19 : $i]: (m1_subset_1 @ (k2_subset_1 @ X19) @ (k1_zfmisc_1 @ X19))),
% 5.12/5.32      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 5.12/5.32  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.12/5.32  thf('57', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 5.12/5.32      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.12/5.32  thf('58', plain, (![X19 : $i]: (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X19))),
% 5.12/5.32      inference('demod', [status(thm)], ['56', '57'])).
% 5.12/5.32  thf('59', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf('60', plain,
% 5.12/5.32      (![X1 : $i, X3 : $i]:
% 5.12/5.32         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.12/5.32      inference('cnf', [status(esa)], [d3_tarski])).
% 5.12/5.32  thf('61', plain,
% 5.12/5.32      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.12/5.32         (~ (r2_hidden @ X8 @ X7)
% 5.12/5.32          | (r2_hidden @ X8 @ X6)
% 5.12/5.32          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 5.12/5.32      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.12/5.32  thf('62', plain,
% 5.12/5.32      (![X5 : $i, X6 : $i, X8 : $i]:
% 5.12/5.32         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 5.12/5.32      inference('simplify', [status(thm)], ['61'])).
% 5.12/5.32  thf('63', plain,
% 5.12/5.32      (![X28 : $i, X29 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 5.12/5.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.12/5.32  thf('64', plain,
% 5.12/5.32      (![X5 : $i, X6 : $i, X8 : $i]:
% 5.12/5.32         ((r2_hidden @ X8 @ X6)
% 5.12/5.32          | ~ (r2_hidden @ X8 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 5.12/5.32      inference('demod', [status(thm)], ['62', '63'])).
% 5.12/5.32  thf('65', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.12/5.32         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 5.12/5.32          | (r2_hidden @ (sk_C @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 5.12/5.32             X0))),
% 5.12/5.32      inference('sup-', [status(thm)], ['60', '64'])).
% 5.12/5.32  thf('66', plain,
% 5.12/5.32      (![X1 : $i, X3 : $i]:
% 5.12/5.32         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.12/5.32      inference('cnf', [status(esa)], [d3_tarski])).
% 5.12/5.32  thf('67', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)
% 5.12/5.32          | (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0))),
% 5.12/5.32      inference('sup-', [status(thm)], ['65', '66'])).
% 5.12/5.32  thf('68', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 5.12/5.32      inference('simplify', [status(thm)], ['67'])).
% 5.12/5.32  thf('69', plain,
% 5.12/5.32      (![X30 : $i, X32 : $i]:
% 5.12/5.32         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 5.12/5.32      inference('cnf', [status(esa)], [t3_subset])).
% 5.12/5.32  thf('70', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 5.12/5.32          (k1_zfmisc_1 @ X0))),
% 5.12/5.32      inference('sup-', [status(thm)], ['68', '69'])).
% 5.12/5.32  thf('71', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 5.12/5.32          (k1_zfmisc_1 @ X1))),
% 5.12/5.32      inference('sup+', [status(thm)], ['59', '70'])).
% 5.12/5.32  thf(t32_subset_1, axiom,
% 5.12/5.32    (![A:$i,B:$i]:
% 5.12/5.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.12/5.32       ( ![C:$i]:
% 5.12/5.32         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.12/5.32           ( ( k7_subset_1 @ A @ B @ C ) =
% 5.12/5.32             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 5.12/5.32  thf('72', plain,
% 5.12/5.32      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.12/5.32         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 5.12/5.32          | ((k7_subset_1 @ X26 @ X27 @ X25)
% 5.12/5.32              = (k9_subset_1 @ X26 @ X27 @ (k3_subset_1 @ X26 @ X25)))
% 5.12/5.32          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 5.12/5.32      inference('cnf', [status(esa)], [t32_subset_1])).
% 5.12/5.32  thf('73', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.12/5.32         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 5.12/5.32          | ((k7_subset_1 @ X0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 5.12/5.32              = (k9_subset_1 @ X0 @ X2 @ 
% 5.12/5.32                 (k3_subset_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))))),
% 5.12/5.32      inference('sup-', [status(thm)], ['71', '72'])).
% 5.12/5.32  thf('74', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf('75', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 5.12/5.32          (k1_zfmisc_1 @ X0))),
% 5.12/5.32      inference('sup-', [status(thm)], ['68', '69'])).
% 5.12/5.32  thf('76', plain,
% 5.12/5.32      (![X17 : $i, X18 : $i]:
% 5.12/5.32         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 5.12/5.32          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 5.12/5.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.12/5.32  thf('77', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k3_subset_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32           = (k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('sup-', [status(thm)], ['75', '76'])).
% 5.12/5.32  thf('78', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k3_subset_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32           = (k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 5.12/5.32      inference('sup+', [status(thm)], ['74', '77'])).
% 5.12/5.32  thf('79', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.12/5.32          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('eq_fact', [status(thm)], ['4'])).
% 5.12/5.32  thf('80', plain,
% 5.12/5.32      (![X5 : $i, X6 : $i, X8 : $i]:
% 5.12/5.32         ((r2_hidden @ X8 @ X6)
% 5.12/5.32          | ~ (r2_hidden @ X8 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 5.12/5.32      inference('demod', [status(thm)], ['62', '63'])).
% 5.12/5.32  thf('81', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.12/5.32         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 5.12/5.32            = (k1_setfam_1 @ 
% 5.12/5.32               (k2_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))
% 5.12/5.32          | (r2_hidden @ 
% 5.12/5.32             (sk_D @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 5.12/5.32              (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2) @ 
% 5.12/5.32             X0))),
% 5.12/5.32      inference('sup-', [status(thm)], ['79', '80'])).
% 5.12/5.32  thf('82', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 5.12/5.32      inference('clc', [status(thm)], ['17', '18'])).
% 5.12/5.32  thf('83', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 5.12/5.32            = (k1_setfam_1 @ 
% 5.12/5.32               (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))
% 5.12/5.32          | ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 5.12/5.32              = (k1_setfam_1 @ 
% 5.12/5.32                 (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))))),
% 5.12/5.32      inference('sup-', [status(thm)], ['81', '82'])).
% 5.12/5.32  thf('84', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 5.12/5.32           = (k1_setfam_1 @ 
% 5.12/5.32              (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 5.12/5.32      inference('simplify', [status(thm)], ['83'])).
% 5.12/5.32  thf(t100_xboole_1, axiom,
% 5.12/5.32    (![A:$i,B:$i]:
% 5.12/5.32     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.12/5.32  thf('85', plain,
% 5.12/5.32      (![X10 : $i, X11 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X10 @ X11)
% 5.12/5.32           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 5.12/5.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.12/5.32  thf('86', plain,
% 5.12/5.32      (![X28 : $i, X29 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 5.12/5.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.12/5.32  thf('87', plain,
% 5.12/5.32      (![X10 : $i, X11 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X10 @ X11)
% 5.12/5.32           = (k5_xboole_0 @ X10 @ (k1_setfam_1 @ (k2_tarski @ X10 @ X11))))),
% 5.12/5.32      inference('demod', [status(thm)], ['85', '86'])).
% 5.12/5.32  thf('88', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('sup+', [status(thm)], ['84', '87'])).
% 5.12/5.32  thf('89', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf('90', plain,
% 5.12/5.32      (![X10 : $i, X11 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X10 @ X11)
% 5.12/5.32           = (k5_xboole_0 @ X10 @ (k1_setfam_1 @ (k2_tarski @ X10 @ X11))))),
% 5.12/5.32      inference('demod', [status(thm)], ['85', '86'])).
% 5.12/5.32  thf('91', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X0 @ X1)
% 5.12/5.32           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('sup+', [status(thm)], ['89', '90'])).
% 5.12/5.32  thf('92', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32           = (k4_xboole_0 @ X0 @ X1))),
% 5.12/5.32      inference('demod', [status(thm)], ['88', '91'])).
% 5.12/5.32  thf('93', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k3_subset_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32           = (k4_xboole_0 @ X1 @ X0))),
% 5.12/5.32      inference('demod', [status(thm)], ['78', '92'])).
% 5.12/5.32  thf('94', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.12/5.32         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 5.12/5.32          | ((k7_subset_1 @ X0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 5.12/5.32              = (k9_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 5.12/5.32      inference('demod', [status(thm)], ['73', '93'])).
% 5.12/5.32  thf('95', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k7_subset_1 @ X0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 5.12/5.32           = (k9_subset_1 @ X0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.12/5.32      inference('sup-', [status(thm)], ['58', '94'])).
% 5.12/5.32  thf('96', plain,
% 5.12/5.32      (![X12 : $i, X13 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 5.12/5.32           = (k1_setfam_1 @ (k2_tarski @ X12 @ X13)))),
% 5.12/5.32      inference('demod', [status(thm)], ['43', '44'])).
% 5.12/5.32  thf('97', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf('98', plain,
% 5.12/5.32      (![X12 : $i, X13 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 5.12/5.32           = (k1_setfam_1 @ (k2_tarski @ X12 @ X13)))),
% 5.12/5.32      inference('demod', [status(thm)], ['43', '44'])).
% 5.12/5.32  thf('99', plain,
% 5.12/5.32      (![X12 : $i, X13 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 5.12/5.32           = (k1_setfam_1 @ (k2_tarski @ X12 @ X13)))),
% 5.12/5.32      inference('demod', [status(thm)], ['43', '44'])).
% 5.12/5.32  thf('100', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32           = (k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 5.12/5.32      inference('sup+', [status(thm)], ['98', '99'])).
% 5.12/5.32  thf('101', plain,
% 5.12/5.32      (![X10 : $i, X11 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X10 @ X11)
% 5.12/5.32           = (k5_xboole_0 @ X10 @ (k1_setfam_1 @ (k2_tarski @ X10 @ X11))))),
% 5.12/5.32      inference('demod', [status(thm)], ['85', '86'])).
% 5.12/5.32  thf('102', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 5.12/5.32           = (k5_xboole_0 @ X1 @ 
% 5.12/5.32              (k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 5.12/5.32      inference('sup+', [status(thm)], ['100', '101'])).
% 5.12/5.32  thf('103', plain,
% 5.12/5.32      (![X12 : $i, X13 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 5.12/5.32           = (k1_setfam_1 @ (k2_tarski @ X12 @ X13)))),
% 5.12/5.32      inference('demod', [status(thm)], ['43', '44'])).
% 5.12/5.32  thf('104', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 5.12/5.32           = (k5_xboole_0 @ X1 @ 
% 5.12/5.32              (k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 5.12/5.32      inference('demod', [status(thm)], ['102', '103'])).
% 5.12/5.32  thf('105', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 5.12/5.32           = (k5_xboole_0 @ X0 @ 
% 5.12/5.32              (k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 5.12/5.32      inference('sup+', [status(thm)], ['97', '104'])).
% 5.12/5.32  thf('106', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32           = (k4_xboole_0 @ X0 @ X1))),
% 5.12/5.32      inference('demod', [status(thm)], ['88', '91'])).
% 5.12/5.32  thf('107', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 5.12/5.32           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.12/5.32      inference('demod', [status(thm)], ['105', '106'])).
% 5.12/5.32  thf('108', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 5.12/5.32           = (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('sup+', [status(thm)], ['96', '107'])).
% 5.12/5.32  thf('109', plain,
% 5.12/5.32      (![X10 : $i, X11 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X10 @ X11)
% 5.12/5.32           = (k5_xboole_0 @ X10 @ (k1_setfam_1 @ (k2_tarski @ X10 @ X11))))),
% 5.12/5.32      inference('demod', [status(thm)], ['85', '86'])).
% 5.12/5.32  thf('110', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 5.12/5.32           = (k4_xboole_0 @ X1 @ X0))),
% 5.12/5.32      inference('demod', [status(thm)], ['108', '109'])).
% 5.12/5.32  thf('111', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf('112', plain, (![X19 : $i]: (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X19))),
% 5.12/5.32      inference('demod', [status(thm)], ['56', '57'])).
% 5.12/5.32  thf(redefinition_k9_subset_1, axiom,
% 5.12/5.32    (![A:$i,B:$i,C:$i]:
% 5.12/5.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.12/5.32       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 5.12/5.32  thf('113', plain,
% 5.12/5.32      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.12/5.32         (((k9_subset_1 @ X24 @ X22 @ X23) = (k3_xboole_0 @ X22 @ X23))
% 5.12/5.32          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 5.12/5.32      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 5.12/5.32  thf('114', plain,
% 5.12/5.32      (![X28 : $i, X29 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 5.12/5.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.12/5.32  thf('115', plain,
% 5.12/5.32      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.12/5.32         (((k9_subset_1 @ X24 @ X22 @ X23)
% 5.12/5.32            = (k1_setfam_1 @ (k2_tarski @ X22 @ X23)))
% 5.12/5.32          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 5.12/5.32      inference('demod', [status(thm)], ['113', '114'])).
% 5.12/5.32  thf('116', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 5.12/5.32      inference('sup-', [status(thm)], ['112', '115'])).
% 5.12/5.32  thf('117', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k9_subset_1 @ X1 @ X0 @ X1) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 5.12/5.32      inference('sup+', [status(thm)], ['111', '116'])).
% 5.12/5.32  thf('118', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k9_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 5.12/5.32           = (k4_xboole_0 @ X1 @ X0))),
% 5.12/5.32      inference('sup+', [status(thm)], ['110', '117'])).
% 5.12/5.32  thf('119', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 5.12/5.32      inference('sup-', [status(thm)], ['112', '115'])).
% 5.12/5.32  thf('120', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 5.12/5.32          (k1_zfmisc_1 @ X0))),
% 5.12/5.32      inference('sup-', [status(thm)], ['68', '69'])).
% 5.12/5.32  thf('121', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 5.12/5.32      inference('sup+', [status(thm)], ['119', '120'])).
% 5.12/5.32  thf('122', plain,
% 5.12/5.32      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.12/5.32         (((k9_subset_1 @ X24 @ X22 @ X23)
% 5.12/5.32            = (k1_setfam_1 @ (k2_tarski @ X22 @ X23)))
% 5.12/5.32          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 5.12/5.32      inference('demod', [status(thm)], ['113', '114'])).
% 5.12/5.32  thf('123', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.12/5.32         ((k9_subset_1 @ X0 @ X2 @ (k9_subset_1 @ X0 @ X1 @ X0))
% 5.12/5.32           = (k1_setfam_1 @ (k2_tarski @ X2 @ (k9_subset_1 @ X0 @ X1 @ X0))))),
% 5.12/5.32      inference('sup-', [status(thm)], ['121', '122'])).
% 5.12/5.32  thf('124', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 5.12/5.32      inference('sup-', [status(thm)], ['112', '115'])).
% 5.12/5.32  thf('125', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 5.12/5.32           = (k1_setfam_1 @ 
% 5.12/5.32              (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 5.12/5.32      inference('simplify', [status(thm)], ['83'])).
% 5.12/5.32  thf('126', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 5.12/5.32           = (k1_setfam_1 @ (k2_tarski @ X0 @ (k9_subset_1 @ X0 @ X1 @ X0))))),
% 5.12/5.32      inference('sup+', [status(thm)], ['124', '125'])).
% 5.12/5.32  thf('127', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 5.12/5.32           = (k9_subset_1 @ X0 @ X0 @ (k9_subset_1 @ X0 @ X1 @ X0)))),
% 5.12/5.32      inference('sup+', [status(thm)], ['123', '126'])).
% 5.12/5.32  thf('128', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1))
% 5.12/5.32           = (k9_subset_1 @ X1 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.12/5.32      inference('sup+', [status(thm)], ['118', '127'])).
% 5.12/5.32  thf('129', plain,
% 5.12/5.32      (![X14 : $i, X15 : $i]:
% 5.12/5.32         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 5.12/5.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.12/5.32  thf('130', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 5.12/5.32           = (k4_xboole_0 @ X1 @ X0))),
% 5.12/5.32      inference('demod', [status(thm)], ['108', '109'])).
% 5.12/5.32  thf('131', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X1 @ X0)
% 5.12/5.32           = (k9_subset_1 @ X1 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.12/5.32      inference('demod', [status(thm)], ['128', '129', '130'])).
% 5.12/5.32  thf('132', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k7_subset_1 @ X0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 5.12/5.32           = (k4_xboole_0 @ X0 @ X1))),
% 5.12/5.32      inference('demod', [status(thm)], ['95', '131'])).
% 5.12/5.32  thf('133', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k7_subset_1 @ X0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 5.12/5.32           = (k4_xboole_0 @ X0 @ X1))),
% 5.12/5.32      inference('sup+', [status(thm)], ['55', '132'])).
% 5.12/5.32  thf('134', plain,
% 5.12/5.32      (((k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('sup+', [status(thm)], ['54', '133'])).
% 5.12/5.32  thf('135', plain,
% 5.12/5.32      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A))) = (sk_B))),
% 5.12/5.32      inference('sup+', [status(thm)], ['24', '53'])).
% 5.12/5.32  thf('136', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X0 @ X1)
% 5.12/5.32           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('sup+', [status(thm)], ['89', '90'])).
% 5.12/5.32  thf('137', plain,
% 5.12/5.32      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('sup+', [status(thm)], ['135', '136'])).
% 5.12/5.32  thf('138', plain,
% 5.12/5.32      (((k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('demod', [status(thm)], ['134', '137'])).
% 5.12/5.32  thf('139', plain,
% 5.12/5.32      (![X33 : $i]:
% 5.12/5.32         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 5.12/5.32      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.12/5.32  thf('140', plain,
% 5.12/5.32      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.12/5.32        | (v4_pre_topc @ sk_B @ sk_A))),
% 5.12/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.12/5.32  thf('141', plain,
% 5.12/5.32      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.12/5.32      inference('split', [status(esa)], ['140'])).
% 5.12/5.32  thf('142', plain,
% 5.12/5.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.12/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.12/5.32  thf(d6_pre_topc, axiom,
% 5.12/5.32    (![A:$i]:
% 5.12/5.32     ( ( l1_pre_topc @ A ) =>
% 5.12/5.32       ( ![B:$i]:
% 5.12/5.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.12/5.32           ( ( v4_pre_topc @ B @ A ) <=>
% 5.12/5.32             ( v3_pre_topc @
% 5.12/5.32               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 5.12/5.32               A ) ) ) ) ))).
% 5.12/5.32  thf('143', plain,
% 5.12/5.32      (![X34 : $i, X35 : $i]:
% 5.12/5.32         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 5.12/5.32          | ~ (v4_pre_topc @ X34 @ X35)
% 5.12/5.32          | (v3_pre_topc @ 
% 5.12/5.32             (k7_subset_1 @ (u1_struct_0 @ X35) @ (k2_struct_0 @ X35) @ X34) @ 
% 5.12/5.32             X35)
% 5.12/5.32          | ~ (l1_pre_topc @ X35))),
% 5.12/5.32      inference('cnf', [status(esa)], [d6_pre_topc])).
% 5.12/5.32  thf('144', plain,
% 5.12/5.32      ((~ (l1_pre_topc @ sk_A)
% 5.12/5.32        | (v3_pre_topc @ 
% 5.12/5.32           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.12/5.32           sk_A)
% 5.12/5.32        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.12/5.32      inference('sup-', [status(thm)], ['142', '143'])).
% 5.12/5.32  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 5.12/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.12/5.32  thf('146', plain,
% 5.12/5.32      (((v3_pre_topc @ 
% 5.12/5.32         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.12/5.32         sk_A)
% 5.12/5.32        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.12/5.32      inference('demod', [status(thm)], ['144', '145'])).
% 5.12/5.32  thf('147', plain,
% 5.12/5.32      (((v3_pre_topc @ 
% 5.12/5.32         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.12/5.32         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.12/5.32      inference('sup-', [status(thm)], ['141', '146'])).
% 5.12/5.32  thf('148', plain,
% 5.12/5.32      ((((v3_pre_topc @ 
% 5.12/5.32          (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.12/5.32          sk_A)
% 5.12/5.32         | ~ (l1_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.12/5.32      inference('sup+', [status(thm)], ['139', '147'])).
% 5.12/5.32  thf('149', plain, ((l1_struct_0 @ sk_A)),
% 5.12/5.32      inference('sup-', [status(thm)], ['31', '32'])).
% 5.12/5.32  thf('150', plain,
% 5.12/5.32      (((v3_pre_topc @ 
% 5.12/5.32         (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.12/5.32         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.12/5.32      inference('demod', [status(thm)], ['148', '149'])).
% 5.12/5.32  thf('151', plain,
% 5.12/5.32      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.12/5.32         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.12/5.32      inference('sup+', [status(thm)], ['138', '150'])).
% 5.12/5.32  thf('152', plain,
% 5.12/5.32      (![X33 : $i]:
% 5.12/5.32         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 5.12/5.32      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.12/5.32  thf('153', plain,
% 5.12/5.32      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 5.12/5.32      inference('simplify', [status(thm)], ['23'])).
% 5.12/5.32  thf('154', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         ((k4_xboole_0 @ X0 @ X1)
% 5.12/5.32           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 5.12/5.32      inference('sup+', [status(thm)], ['89', '90'])).
% 5.12/5.32  thf('155', plain,
% 5.12/5.32      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('sup+', [status(thm)], ['153', '154'])).
% 5.12/5.32  thf('156', plain,
% 5.12/5.32      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('sup-', [status(thm)], ['27', '28'])).
% 5.12/5.32  thf('157', plain,
% 5.12/5.32      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.12/5.32         <= (~
% 5.12/5.32             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('split', [status(esa)], ['0'])).
% 5.12/5.32  thf('158', plain,
% 5.12/5.32      ((~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.12/5.32         <= (~
% 5.12/5.32             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('sup-', [status(thm)], ['156', '157'])).
% 5.12/5.32  thf('159', plain,
% 5.12/5.32      ((~ (v3_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.12/5.32         <= (~
% 5.12/5.32             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('sup-', [status(thm)], ['155', '158'])).
% 5.12/5.32  thf('160', plain,
% 5.12/5.32      (((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.12/5.32         | ~ (l1_struct_0 @ sk_A)))
% 5.12/5.32         <= (~
% 5.12/5.32             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('sup-', [status(thm)], ['152', '159'])).
% 5.12/5.32  thf('161', plain, ((l1_struct_0 @ sk_A)),
% 5.12/5.32      inference('sup-', [status(thm)], ['31', '32'])).
% 5.12/5.32  thf('162', plain,
% 5.12/5.32      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.12/5.32         <= (~
% 5.12/5.32             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('demod', [status(thm)], ['160', '161'])).
% 5.12/5.32  thf('163', plain,
% 5.12/5.32      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 5.12/5.32       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.12/5.32      inference('sup-', [status(thm)], ['151', '162'])).
% 5.12/5.32  thf('164', plain,
% 5.12/5.32      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 5.12/5.32       ((v4_pre_topc @ sk_B @ sk_A))),
% 5.12/5.32      inference('split', [status(esa)], ['140'])).
% 5.12/5.32  thf('165', plain,
% 5.12/5.32      (![X33 : $i]:
% 5.12/5.32         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 5.12/5.32      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.12/5.32  thf('166', plain,
% 5.12/5.32      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('sup+', [status(thm)], ['153', '154'])).
% 5.12/5.32  thf('167', plain,
% 5.12/5.32      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('sup-', [status(thm)], ['27', '28'])).
% 5.12/5.32  thf('168', plain,
% 5.12/5.32      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.12/5.32         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('split', [status(esa)], ['140'])).
% 5.12/5.32  thf('169', plain,
% 5.12/5.32      (((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.12/5.32         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('sup+', [status(thm)], ['167', '168'])).
% 5.12/5.32  thf('170', plain,
% 5.12/5.32      (((v3_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.12/5.32         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('sup+', [status(thm)], ['166', '169'])).
% 5.12/5.32  thf('171', plain,
% 5.12/5.32      ((((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.12/5.32         | ~ (l1_struct_0 @ sk_A)))
% 5.12/5.32         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('sup+', [status(thm)], ['165', '170'])).
% 5.12/5.32  thf('172', plain, ((l1_struct_0 @ sk_A)),
% 5.12/5.32      inference('sup-', [status(thm)], ['31', '32'])).
% 5.12/5.32  thf('173', plain,
% 5.12/5.32      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.12/5.32         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('demod', [status(thm)], ['171', '172'])).
% 5.12/5.32  thf('174', plain,
% 5.12/5.32      (((k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.12/5.32         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.12/5.32      inference('demod', [status(thm)], ['134', '137'])).
% 5.12/5.32  thf('175', plain,
% 5.12/5.32      (![X33 : $i]:
% 5.12/5.32         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 5.12/5.32      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.12/5.32  thf('176', plain,
% 5.12/5.32      (![X34 : $i, X35 : $i]:
% 5.12/5.32         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 5.12/5.32          | ~ (v3_pre_topc @ 
% 5.12/5.32               (k7_subset_1 @ (u1_struct_0 @ X35) @ (k2_struct_0 @ X35) @ X34) @ 
% 5.12/5.32               X35)
% 5.12/5.32          | (v4_pre_topc @ X34 @ X35)
% 5.12/5.32          | ~ (l1_pre_topc @ X35))),
% 5.12/5.32      inference('cnf', [status(esa)], [d6_pre_topc])).
% 5.12/5.32  thf('177', plain,
% 5.12/5.32      (![X0 : $i, X1 : $i]:
% 5.12/5.32         (~ (v3_pre_topc @ 
% 5.12/5.32             (k7_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1) @ X0)
% 5.12/5.32          | ~ (l1_struct_0 @ X0)
% 5.12/5.32          | ~ (l1_pre_topc @ X0)
% 5.12/5.32          | (v4_pre_topc @ X1 @ X0)
% 5.12/5.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 5.12/5.32      inference('sup-', [status(thm)], ['175', '176'])).
% 5.12/5.32  thf('178', plain,
% 5.12/5.32      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.12/5.32        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.12/5.32        | (v4_pre_topc @ sk_B @ sk_A)
% 5.12/5.32        | ~ (l1_pre_topc @ sk_A)
% 5.12/5.32        | ~ (l1_struct_0 @ sk_A))),
% 5.12/5.32      inference('sup-', [status(thm)], ['174', '177'])).
% 5.12/5.32  thf('179', plain,
% 5.12/5.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.12/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.12/5.32  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 5.12/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.12/5.32  thf('181', plain, ((l1_struct_0 @ sk_A)),
% 5.12/5.32      inference('sup-', [status(thm)], ['31', '32'])).
% 5.12/5.32  thf('182', plain,
% 5.12/5.32      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.12/5.32        | (v4_pre_topc @ sk_B @ sk_A))),
% 5.12/5.32      inference('demod', [status(thm)], ['178', '179', '180', '181'])).
% 5.12/5.32  thf('183', plain,
% 5.12/5.32      (((v4_pre_topc @ sk_B @ sk_A))
% 5.12/5.32         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.12/5.32      inference('sup-', [status(thm)], ['173', '182'])).
% 5.12/5.32  thf('184', plain,
% 5.12/5.32      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 5.12/5.32      inference('split', [status(esa)], ['0'])).
% 5.12/5.32  thf('185', plain,
% 5.12/5.32      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 5.12/5.32       ((v4_pre_topc @ sk_B @ sk_A))),
% 5.12/5.32      inference('sup-', [status(thm)], ['183', '184'])).
% 5.12/5.32  thf('186', plain, ($false),
% 5.12/5.32      inference('sat_resolution*', [status(thm)], ['1', '163', '164', '185'])).
% 5.12/5.32  
% 5.12/5.32  % SZS output end Refutation
% 5.12/5.32  
% 5.12/5.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
