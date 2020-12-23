%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OunXICWycw

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:32 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 580 expanded)
%              Number of leaves         :   51 ( 190 expanded)
%              Depth                    :   16
%              Number of atoms          : 1585 (5991 expanded)
%              Number of equality atoms :  103 ( 389 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(t94_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( ( v3_tops_1 @ B @ A )
              <=> ( B
                  = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k2_tops_1 @ X41 @ X40 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k2_pre_topc @ X41 @ X40 ) @ ( k1_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( v2_tops_1 @ X46 @ X47 )
      | ~ ( v3_tops_1 @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tops_1 @ X42 @ X43 )
      | ( ( k1_tops_1 @ X43 @ X42 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( r1_tarski @ X44 @ ( k2_tops_1 @ X45 @ X44 ) )
      | ( v2_tops_1 @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t93_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v2_tops_1 @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('32',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( v3_tops_1 @ X48 @ X49 )
      | ~ ( v4_pre_topc @ X48 @ X49 )
      | ~ ( v2_tops_1 @ X48 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t93_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('39',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('41',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['20','39','40'])).

thf('42',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','41'])).

thf('43',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','42'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('44',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('49',plain,(
    ! [X35: $i] :
      ( ( l1_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('53',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('54',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('55',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('56',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('59',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('63',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['56'])).

thf('68',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('70',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('71',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('72',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('76',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('77',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('80',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('83',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('85',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['77','86'])).

thf('88',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['74','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','88'])).

thf('90',plain,
    ( ( m1_subset_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['44','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('92',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t53_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('94',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v3_pre_topc @ X38 @ X39 )
      | ( ( k2_pre_topc @ X39 @ ( k7_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_struct_0 @ X39 ) @ X38 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_struct_0 @ X39 ) @ X38 ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t53_pre_topc])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('100',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v4_pre_topc @ X33 @ X34 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_struct_0 @ X34 ) @ X33 ) @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['98','104'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('106',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X17 ) @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('107',plain,(
    ! [X14: $i] :
      ( ( k2_subset_1 @ X14 )
      = X14 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('108',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('109',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('112',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('113',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['105','110','111','112'])).

thf('114',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['74','87'])).

thf('115',plain,(
    v3_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['97','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('118',plain,(
    v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
            = B ) ) ) )).

thf('121',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k2_struct_0 @ X37 ) @ ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k2_struct_0 @ X37 ) @ X36 ) )
        = X36 )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t22_pre_topc])).

thf('122',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('124',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['119','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('127',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('129',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('131',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('133',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('135',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['125','126','133','134'])).

thf('136',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['125','126','133','134'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('139',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['96','118','135','136','137','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('143',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('144',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['43','139','142','143'])).

thf('145',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['19'])).

thf('146',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['20','39'])).

thf('147',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['145','146'])).

thf('148',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['144','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OunXICWycw
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:24:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.33/2.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.33/2.56  % Solved by: fo/fo7.sh
% 2.33/2.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.33/2.56  % done 2273 iterations in 2.098s
% 2.33/2.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.33/2.56  % SZS output start Refutation
% 2.33/2.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.33/2.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.33/2.56  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 2.33/2.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.33/2.56  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.33/2.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.33/2.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.33/2.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.33/2.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.33/2.56  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.33/2.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.33/2.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.33/2.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.33/2.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.33/2.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.33/2.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.33/2.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.33/2.56  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 2.33/2.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.33/2.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.33/2.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.33/2.56  thf(sk_A_type, type, sk_A: $i).
% 2.33/2.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.33/2.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.33/2.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.33/2.56  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.33/2.56  thf(sk_B_type, type, sk_B: $i).
% 2.33/2.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 2.33/2.56  thf(t94_tops_1, conjecture,
% 2.33/2.56    (![A:$i]:
% 2.33/2.56     ( ( l1_pre_topc @ A ) =>
% 2.33/2.56       ( ![B:$i]:
% 2.33/2.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.56           ( ( v4_pre_topc @ B @ A ) =>
% 2.33/2.56             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 2.33/2.56  thf(zf_stmt_0, negated_conjecture,
% 2.33/2.56    (~( ![A:$i]:
% 2.33/2.56        ( ( l1_pre_topc @ A ) =>
% 2.33/2.56          ( ![B:$i]:
% 2.33/2.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.56              ( ( v4_pre_topc @ B @ A ) =>
% 2.33/2.56                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 2.33/2.56    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 2.33/2.56  thf('0', plain,
% 2.33/2.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf(l78_tops_1, axiom,
% 2.33/2.56    (![A:$i]:
% 2.33/2.56     ( ( l1_pre_topc @ A ) =>
% 2.33/2.56       ( ![B:$i]:
% 2.33/2.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.56           ( ( k2_tops_1 @ A @ B ) =
% 2.33/2.56             ( k7_subset_1 @
% 2.33/2.56               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.33/2.56               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.33/2.56  thf('1', plain,
% 2.33/2.56      (![X40 : $i, X41 : $i]:
% 2.33/2.56         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 2.33/2.56          | ((k2_tops_1 @ X41 @ X40)
% 2.33/2.56              = (k7_subset_1 @ (u1_struct_0 @ X41) @ 
% 2.33/2.56                 (k2_pre_topc @ X41 @ X40) @ (k1_tops_1 @ X41 @ X40)))
% 2.33/2.56          | ~ (l1_pre_topc @ X41))),
% 2.33/2.56      inference('cnf', [status(esa)], [l78_tops_1])).
% 2.33/2.56  thf('2', plain,
% 2.33/2.56      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.56        | ((k2_tops_1 @ sk_A @ sk_B)
% 2.33/2.56            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.33/2.56               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.56      inference('sup-', [status(thm)], ['0', '1'])).
% 2.33/2.56  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('4', plain,
% 2.33/2.56      (((k2_tops_1 @ sk_A @ sk_B)
% 2.33/2.56         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.33/2.56            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.56      inference('demod', [status(thm)], ['2', '3'])).
% 2.33/2.56  thf('5', plain,
% 2.33/2.56      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('6', plain,
% 2.33/2.56      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 2.33/2.56      inference('split', [status(esa)], ['5'])).
% 2.33/2.56  thf('7', plain,
% 2.33/2.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf(t92_tops_1, axiom,
% 2.33/2.56    (![A:$i]:
% 2.33/2.56     ( ( l1_pre_topc @ A ) =>
% 2.33/2.56       ( ![B:$i]:
% 2.33/2.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.56           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 2.33/2.56  thf('8', plain,
% 2.33/2.56      (![X46 : $i, X47 : $i]:
% 2.33/2.56         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 2.33/2.56          | (v2_tops_1 @ X46 @ X47)
% 2.33/2.56          | ~ (v3_tops_1 @ X46 @ X47)
% 2.33/2.56          | ~ (l1_pre_topc @ X47))),
% 2.33/2.56      inference('cnf', [status(esa)], [t92_tops_1])).
% 2.33/2.56  thf('9', plain,
% 2.33/2.56      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.56        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 2.33/2.56        | (v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.56      inference('sup-', [status(thm)], ['7', '8'])).
% 2.33/2.56  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('11', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.56      inference('demod', [status(thm)], ['9', '10'])).
% 2.33/2.56  thf('12', plain,
% 2.33/2.56      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 2.33/2.56      inference('sup-', [status(thm)], ['6', '11'])).
% 2.33/2.56  thf('13', plain,
% 2.33/2.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf(t84_tops_1, axiom,
% 2.33/2.56    (![A:$i]:
% 2.33/2.56     ( ( l1_pre_topc @ A ) =>
% 2.33/2.56       ( ![B:$i]:
% 2.33/2.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.56           ( ( v2_tops_1 @ B @ A ) <=>
% 2.33/2.56             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 2.33/2.56  thf('14', plain,
% 2.33/2.56      (![X42 : $i, X43 : $i]:
% 2.33/2.56         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 2.33/2.56          | ~ (v2_tops_1 @ X42 @ X43)
% 2.33/2.56          | ((k1_tops_1 @ X43 @ X42) = (k1_xboole_0))
% 2.33/2.56          | ~ (l1_pre_topc @ X43))),
% 2.33/2.56      inference('cnf', [status(esa)], [t84_tops_1])).
% 2.33/2.56  thf('15', plain,
% 2.33/2.56      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.56        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 2.33/2.56        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.56      inference('sup-', [status(thm)], ['13', '14'])).
% 2.33/2.56  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('17', plain,
% 2.33/2.56      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 2.33/2.56        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 2.33/2.56      inference('demod', [status(thm)], ['15', '16'])).
% 2.33/2.56  thf('18', plain,
% 2.33/2.56      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 2.33/2.56         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 2.33/2.56      inference('sup-', [status(thm)], ['12', '17'])).
% 2.33/2.56  thf('19', plain,
% 2.33/2.56      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('20', plain,
% 2.33/2.56      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 2.33/2.56      inference('split', [status(esa)], ['19'])).
% 2.33/2.56  thf('21', plain,
% 2.33/2.56      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 2.33/2.56         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.56      inference('split', [status(esa)], ['5'])).
% 2.33/2.56  thf('22', plain,
% 2.33/2.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf(t88_tops_1, axiom,
% 2.33/2.56    (![A:$i]:
% 2.33/2.56     ( ( l1_pre_topc @ A ) =>
% 2.33/2.56       ( ![B:$i]:
% 2.33/2.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.56           ( ( v2_tops_1 @ B @ A ) <=>
% 2.33/2.56             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.33/2.56  thf('23', plain,
% 2.33/2.56      (![X44 : $i, X45 : $i]:
% 2.33/2.56         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 2.33/2.56          | ~ (r1_tarski @ X44 @ (k2_tops_1 @ X45 @ X44))
% 2.33/2.56          | (v2_tops_1 @ X44 @ X45)
% 2.33/2.56          | ~ (l1_pre_topc @ X45))),
% 2.33/2.56      inference('cnf', [status(esa)], [t88_tops_1])).
% 2.33/2.56  thf('24', plain,
% 2.33/2.56      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.56        | (v2_tops_1 @ sk_B @ sk_A)
% 2.33/2.56        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.56      inference('sup-', [status(thm)], ['22', '23'])).
% 2.33/2.56  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('26', plain,
% 2.33/2.56      (((v2_tops_1 @ sk_B @ sk_A)
% 2.33/2.56        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.56      inference('demod', [status(thm)], ['24', '25'])).
% 2.33/2.56  thf('27', plain,
% 2.33/2.56      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 2.33/2.56         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.56      inference('sup-', [status(thm)], ['21', '26'])).
% 2.33/2.56  thf(d10_xboole_0, axiom,
% 2.33/2.56    (![A:$i,B:$i]:
% 2.33/2.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.33/2.56  thf('28', plain,
% 2.33/2.56      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 2.33/2.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.33/2.56  thf('29', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 2.33/2.56      inference('simplify', [status(thm)], ['28'])).
% 2.33/2.56  thf('30', plain,
% 2.33/2.56      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.56      inference('demod', [status(thm)], ['27', '29'])).
% 2.33/2.56  thf('31', plain,
% 2.33/2.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf(t93_tops_1, axiom,
% 2.33/2.56    (![A:$i]:
% 2.33/2.56     ( ( l1_pre_topc @ A ) =>
% 2.33/2.56       ( ![B:$i]:
% 2.33/2.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.56           ( ( ( v2_tops_1 @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 2.33/2.56             ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 2.33/2.56  thf('32', plain,
% 2.33/2.56      (![X48 : $i, X49 : $i]:
% 2.33/2.56         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 2.33/2.56          | (v3_tops_1 @ X48 @ X49)
% 2.33/2.56          | ~ (v4_pre_topc @ X48 @ X49)
% 2.33/2.56          | ~ (v2_tops_1 @ X48 @ X49)
% 2.33/2.56          | ~ (l1_pre_topc @ X49))),
% 2.33/2.56      inference('cnf', [status(esa)], [t93_tops_1])).
% 2.33/2.56  thf('33', plain,
% 2.33/2.56      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.56        | ~ (v2_tops_1 @ sk_B @ sk_A)
% 2.33/2.56        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 2.33/2.56        | (v3_tops_1 @ sk_B @ sk_A))),
% 2.33/2.56      inference('sup-', [status(thm)], ['31', '32'])).
% 2.33/2.56  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('35', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('36', plain, ((~ (v2_tops_1 @ sk_B @ sk_A) | (v3_tops_1 @ sk_B @ sk_A))),
% 2.33/2.56      inference('demod', [status(thm)], ['33', '34', '35'])).
% 2.33/2.56  thf('37', plain,
% 2.33/2.56      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.56      inference('sup-', [status(thm)], ['30', '36'])).
% 2.33/2.56  thf('38', plain,
% 2.33/2.56      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 2.33/2.56      inference('split', [status(esa)], ['19'])).
% 2.33/2.57  thf('39', plain,
% 2.33/2.57      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.57      inference('sup-', [status(thm)], ['37', '38'])).
% 2.33/2.57  thf('40', plain,
% 2.33/2.57      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.57      inference('split', [status(esa)], ['5'])).
% 2.33/2.57  thf('41', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 2.33/2.57      inference('sat_resolution*', [status(thm)], ['20', '39', '40'])).
% 2.33/2.57  thf('42', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 2.33/2.57      inference('simpl_trail', [status(thm)], ['18', '41'])).
% 2.33/2.57  thf('43', plain,
% 2.33/2.57      (((k2_tops_1 @ sk_A @ sk_B)
% 2.33/2.57         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.33/2.57            k1_xboole_0))),
% 2.33/2.57      inference('demod', [status(thm)], ['4', '42'])).
% 2.33/2.57  thf(d3_struct_0, axiom,
% 2.33/2.57    (![A:$i]:
% 2.33/2.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.33/2.57  thf('44', plain,
% 2.33/2.57      (![X32 : $i]:
% 2.33/2.57         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.33/2.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.33/2.57  thf('45', plain,
% 2.33/2.57      (![X32 : $i]:
% 2.33/2.57         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.33/2.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.33/2.57  thf('46', plain,
% 2.33/2.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf('47', plain,
% 2.33/2.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.33/2.57        | ~ (l1_struct_0 @ sk_A))),
% 2.33/2.57      inference('sup+', [status(thm)], ['45', '46'])).
% 2.33/2.57  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf(dt_l1_pre_topc, axiom,
% 2.33/2.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.33/2.57  thf('49', plain,
% 2.33/2.57      (![X35 : $i]: ((l1_struct_0 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.33/2.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.33/2.57  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 2.33/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.33/2.57  thf('51', plain,
% 2.33/2.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 2.33/2.57      inference('demod', [status(thm)], ['47', '50'])).
% 2.33/2.57  thf(dt_k3_subset_1, axiom,
% 2.33/2.57    (![A:$i,B:$i]:
% 2.33/2.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.57       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.33/2.57  thf('52', plain,
% 2.33/2.57      (![X18 : $i, X19 : $i]:
% 2.33/2.57         ((m1_subset_1 @ (k3_subset_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 2.33/2.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 2.33/2.57      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.33/2.57  thf('53', plain,
% 2.33/2.57      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.57        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 2.33/2.57      inference('sup-', [status(thm)], ['51', '52'])).
% 2.33/2.57  thf(d4_xboole_0, axiom,
% 2.33/2.57    (![A:$i,B:$i,C:$i]:
% 2.33/2.57     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.33/2.57       ( ![D:$i]:
% 2.33/2.57         ( ( r2_hidden @ D @ C ) <=>
% 2.33/2.57           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.33/2.57  thf('54', plain,
% 2.33/2.57      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.33/2.57         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.33/2.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.33/2.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.33/2.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.33/2.57  thf(t12_setfam_1, axiom,
% 2.33/2.57    (![A:$i,B:$i]:
% 2.33/2.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.33/2.57  thf('55', plain,
% 2.33/2.57      (![X27 : $i, X28 : $i]:
% 2.33/2.57         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 2.33/2.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.33/2.57  thf('56', plain,
% 2.33/2.57      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.33/2.57         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 2.33/2.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.33/2.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.33/2.57      inference('demod', [status(thm)], ['54', '55'])).
% 2.33/2.57  thf('57', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i]:
% 2.33/2.57         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.33/2.57          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 2.33/2.57      inference('eq_fact', [status(thm)], ['56'])).
% 2.33/2.57  thf('58', plain,
% 2.33/2.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf(l3_subset_1, axiom,
% 2.33/2.57    (![A:$i,B:$i]:
% 2.33/2.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 2.33/2.57  thf('59', plain,
% 2.33/2.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.33/2.57         (~ (r2_hidden @ X20 @ X21)
% 2.33/2.57          | (r2_hidden @ X20 @ X22)
% 2.33/2.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 2.33/2.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.33/2.57  thf('60', plain,
% 2.33/2.57      (![X0 : $i]:
% 2.33/2.57         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 2.33/2.57      inference('sup-', [status(thm)], ['58', '59'])).
% 2.33/2.57  thf('61', plain,
% 2.33/2.57      (![X0 : $i]:
% 2.33/2.57         (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)))
% 2.33/2.57          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.33/2.57      inference('sup-', [status(thm)], ['57', '60'])).
% 2.33/2.57  thf('62', plain,
% 2.33/2.57      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.33/2.57         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.33/2.57          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.33/2.57          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.33/2.57          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.33/2.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.33/2.57  thf('63', plain,
% 2.33/2.57      (![X27 : $i, X28 : $i]:
% 2.33/2.57         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 2.33/2.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.33/2.57  thf('64', plain,
% 2.33/2.57      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.33/2.57         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 2.33/2.57          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.33/2.57          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.33/2.57          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.33/2.57      inference('demod', [status(thm)], ['62', '63'])).
% 2.33/2.57  thf('65', plain,
% 2.33/2.57      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))
% 2.33/2.57        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 2.33/2.57        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 2.33/2.57        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A)))))),
% 2.33/2.57      inference('sup-', [status(thm)], ['61', '64'])).
% 2.33/2.57  thf('66', plain,
% 2.33/2.57      ((~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 2.33/2.57        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A)))))),
% 2.33/2.57      inference('simplify', [status(thm)], ['65'])).
% 2.33/2.57  thf('67', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i]:
% 2.33/2.57         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.33/2.57          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 2.33/2.57      inference('eq_fact', [status(thm)], ['56'])).
% 2.33/2.57  thf('68', plain,
% 2.33/2.57      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 2.33/2.57      inference('clc', [status(thm)], ['66', '67'])).
% 2.33/2.57  thf(commutativity_k2_tarski, axiom,
% 2.33/2.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.33/2.57  thf('69', plain,
% 2.33/2.57      (![X12 : $i, X13 : $i]:
% 2.33/2.57         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 2.33/2.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.33/2.57  thf(t100_xboole_1, axiom,
% 2.33/2.57    (![A:$i,B:$i]:
% 2.33/2.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.33/2.57  thf('70', plain,
% 2.33/2.57      (![X9 : $i, X10 : $i]:
% 2.33/2.57         ((k4_xboole_0 @ X9 @ X10)
% 2.33/2.57           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 2.33/2.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.33/2.57  thf('71', plain,
% 2.33/2.57      (![X27 : $i, X28 : $i]:
% 2.33/2.57         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 2.33/2.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.33/2.57  thf('72', plain,
% 2.33/2.57      (![X9 : $i, X10 : $i]:
% 2.33/2.57         ((k4_xboole_0 @ X9 @ X10)
% 2.33/2.57           = (k5_xboole_0 @ X9 @ (k1_setfam_1 @ (k2_tarski @ X9 @ X10))))),
% 2.33/2.57      inference('demod', [status(thm)], ['70', '71'])).
% 2.33/2.57  thf('73', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i]:
% 2.33/2.57         ((k4_xboole_0 @ X0 @ X1)
% 2.33/2.57           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 2.33/2.57      inference('sup+', [status(thm)], ['69', '72'])).
% 2.33/2.57  thf('74', plain,
% 2.33/2.57      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('sup+', [status(thm)], ['68', '73'])).
% 2.33/2.57  thf('75', plain,
% 2.33/2.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf(d5_subset_1, axiom,
% 2.33/2.57    (![A:$i,B:$i]:
% 2.33/2.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.33/2.57  thf('76', plain,
% 2.33/2.57      (![X15 : $i, X16 : $i]:
% 2.33/2.57         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 2.33/2.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 2.33/2.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.33/2.57  thf('77', plain,
% 2.33/2.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('sup-', [status(thm)], ['75', '76'])).
% 2.33/2.57  thf('78', plain,
% 2.33/2.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 2.33/2.57      inference('demod', [status(thm)], ['47', '50'])).
% 2.33/2.57  thf('79', plain,
% 2.33/2.57      (![X15 : $i, X16 : $i]:
% 2.33/2.57         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 2.33/2.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 2.33/2.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.33/2.57  thf('80', plain,
% 2.33/2.57      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('sup-', [status(thm)], ['78', '79'])).
% 2.33/2.57  thf('81', plain,
% 2.33/2.57      (![X32 : $i]:
% 2.33/2.57         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.33/2.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.33/2.57  thf('82', plain,
% 2.33/2.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('sup-', [status(thm)], ['75', '76'])).
% 2.33/2.57  thf('83', plain,
% 2.33/2.57      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 2.33/2.57        | ~ (l1_struct_0 @ sk_A))),
% 2.33/2.57      inference('sup+', [status(thm)], ['81', '82'])).
% 2.33/2.57  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 2.33/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.33/2.57  thf('85', plain,
% 2.33/2.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('demod', [status(thm)], ['83', '84'])).
% 2.33/2.57  thf('86', plain,
% 2.33/2.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('sup+', [status(thm)], ['80', '85'])).
% 2.33/2.57  thf('87', plain,
% 2.33/2.57      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('demod', [status(thm)], ['77', '86'])).
% 2.33/2.57  thf('88', plain,
% 2.33/2.57      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('sup+', [status(thm)], ['74', '87'])).
% 2.33/2.57  thf('89', plain,
% 2.33/2.57      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.57        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 2.33/2.57      inference('demod', [status(thm)], ['53', '88'])).
% 2.33/2.57  thf('90', plain,
% 2.33/2.57      (((m1_subset_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.57         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.33/2.57        | ~ (l1_struct_0 @ sk_A))),
% 2.33/2.57      inference('sup+', [status(thm)], ['44', '89'])).
% 2.33/2.57  thf('91', plain, ((l1_struct_0 @ sk_A)),
% 2.33/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.33/2.57  thf('92', plain,
% 2.33/2.57      ((m1_subset_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.57        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 2.33/2.57      inference('demod', [status(thm)], ['90', '91'])).
% 2.33/2.57  thf('93', plain,
% 2.33/2.57      (![X32 : $i]:
% 2.33/2.57         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.33/2.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.33/2.57  thf(t53_pre_topc, axiom,
% 2.33/2.57    (![A:$i]:
% 2.33/2.57     ( ( l1_pre_topc @ A ) =>
% 2.33/2.57       ( ![B:$i]:
% 2.33/2.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.57           ( ( ( v3_pre_topc @ B @ A ) =>
% 2.33/2.57               ( ( k2_pre_topc @
% 2.33/2.57                   A @ 
% 2.33/2.57                   ( k7_subset_1 @
% 2.33/2.57                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 2.33/2.57                 ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) & 
% 2.33/2.57             ( ( ( v2_pre_topc @ A ) & 
% 2.33/2.57                 ( ( k2_pre_topc @
% 2.33/2.57                     A @ 
% 2.33/2.57                     ( k7_subset_1 @
% 2.33/2.57                       ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 2.33/2.57                   ( k7_subset_1 @
% 2.33/2.57                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) =>
% 2.33/2.57               ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 2.33/2.57  thf('94', plain,
% 2.33/2.57      (![X38 : $i, X39 : $i]:
% 2.33/2.57         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 2.33/2.57          | ~ (v3_pre_topc @ X38 @ X39)
% 2.33/2.57          | ((k2_pre_topc @ X39 @ 
% 2.33/2.57              (k7_subset_1 @ (u1_struct_0 @ X39) @ (k2_struct_0 @ X39) @ X38))
% 2.33/2.57              = (k7_subset_1 @ (u1_struct_0 @ X39) @ (k2_struct_0 @ X39) @ X38))
% 2.33/2.57          | ~ (l1_pre_topc @ X39))),
% 2.33/2.57      inference('cnf', [status(esa)], [t53_pre_topc])).
% 2.33/2.57  thf('95', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i]:
% 2.33/2.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 2.33/2.57          | ~ (l1_struct_0 @ X0)
% 2.33/2.57          | ~ (l1_pre_topc @ X0)
% 2.33/2.57          | ((k2_pre_topc @ X0 @ 
% 2.33/2.57              (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1))
% 2.33/2.57              = (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1))
% 2.33/2.57          | ~ (v3_pre_topc @ X1 @ X0))),
% 2.33/2.57      inference('sup-', [status(thm)], ['93', '94'])).
% 2.33/2.57  thf('96', plain,
% 2.33/2.57      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 2.33/2.57        | ((k2_pre_topc @ sk_A @ 
% 2.33/2.57            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 2.33/2.57             (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 2.33/2.57            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 2.33/2.57               (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 2.33/2.57        | ~ (l1_pre_topc @ sk_A)
% 2.33/2.57        | ~ (l1_struct_0 @ sk_A))),
% 2.33/2.57      inference('sup-', [status(thm)], ['92', '95'])).
% 2.33/2.57  thf('97', plain,
% 2.33/2.57      (![X32 : $i]:
% 2.33/2.57         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.33/2.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.33/2.57  thf('98', plain,
% 2.33/2.57      (![X32 : $i]:
% 2.33/2.57         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.33/2.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.33/2.57  thf('99', plain,
% 2.33/2.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf(d6_pre_topc, axiom,
% 2.33/2.57    (![A:$i]:
% 2.33/2.57     ( ( l1_pre_topc @ A ) =>
% 2.33/2.57       ( ![B:$i]:
% 2.33/2.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.57           ( ( v4_pre_topc @ B @ A ) <=>
% 2.33/2.57             ( v3_pre_topc @
% 2.33/2.57               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 2.33/2.57               A ) ) ) ) ))).
% 2.33/2.57  thf('100', plain,
% 2.33/2.57      (![X33 : $i, X34 : $i]:
% 2.33/2.57         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 2.33/2.57          | ~ (v4_pre_topc @ X33 @ X34)
% 2.33/2.57          | (v3_pre_topc @ 
% 2.33/2.57             (k7_subset_1 @ (u1_struct_0 @ X34) @ (k2_struct_0 @ X34) @ X33) @ 
% 2.33/2.57             X34)
% 2.33/2.57          | ~ (l1_pre_topc @ X34))),
% 2.33/2.57      inference('cnf', [status(esa)], [d6_pre_topc])).
% 2.33/2.57  thf('101', plain,
% 2.33/2.57      ((~ (l1_pre_topc @ sk_A)
% 2.33/2.57        | (v3_pre_topc @ 
% 2.33/2.57           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.57           sk_A)
% 2.33/2.57        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.33/2.57      inference('sup-', [status(thm)], ['99', '100'])).
% 2.33/2.57  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf('103', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf('104', plain,
% 2.33/2.57      ((v3_pre_topc @ 
% 2.33/2.57        (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.57        sk_A)),
% 2.33/2.57      inference('demod', [status(thm)], ['101', '102', '103'])).
% 2.33/2.57  thf('105', plain,
% 2.33/2.57      (((v3_pre_topc @ 
% 2.33/2.57         (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 2.33/2.57         sk_A)
% 2.33/2.57        | ~ (l1_struct_0 @ sk_A))),
% 2.33/2.57      inference('sup+', [status(thm)], ['98', '104'])).
% 2.33/2.57  thf(dt_k2_subset_1, axiom,
% 2.33/2.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.33/2.57  thf('106', plain,
% 2.33/2.57      (![X17 : $i]: (m1_subset_1 @ (k2_subset_1 @ X17) @ (k1_zfmisc_1 @ X17))),
% 2.33/2.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 2.33/2.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.33/2.57  thf('107', plain, (![X14 : $i]: ((k2_subset_1 @ X14) = (X14))),
% 2.33/2.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.33/2.57  thf('108', plain, (![X17 : $i]: (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X17))),
% 2.33/2.57      inference('demod', [status(thm)], ['106', '107'])).
% 2.33/2.57  thf(redefinition_k7_subset_1, axiom,
% 2.33/2.57    (![A:$i,B:$i,C:$i]:
% 2.33/2.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.57       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.33/2.57  thf('109', plain,
% 2.33/2.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.33/2.57         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 2.33/2.57          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 2.33/2.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.33/2.57  thf('110', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i]:
% 2.33/2.57         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 2.33/2.57      inference('sup-', [status(thm)], ['108', '109'])).
% 2.33/2.57  thf('111', plain,
% 2.33/2.57      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('sup-', [status(thm)], ['78', '79'])).
% 2.33/2.57  thf('112', plain, ((l1_struct_0 @ sk_A)),
% 2.33/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.33/2.57  thf('113', plain,
% 2.33/2.57      ((v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 2.33/2.57      inference('demod', [status(thm)], ['105', '110', '111', '112'])).
% 2.33/2.57  thf('114', plain,
% 2.33/2.57      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('sup+', [status(thm)], ['74', '87'])).
% 2.33/2.57  thf('115', plain,
% 2.33/2.57      ((v3_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 2.33/2.57      inference('demod', [status(thm)], ['113', '114'])).
% 2.33/2.57  thf('116', plain,
% 2.33/2.57      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 2.33/2.57        | ~ (l1_struct_0 @ sk_A))),
% 2.33/2.57      inference('sup+', [status(thm)], ['97', '115'])).
% 2.33/2.57  thf('117', plain, ((l1_struct_0 @ sk_A)),
% 2.33/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.33/2.57  thf('118', plain,
% 2.33/2.57      ((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 2.33/2.57      inference('demod', [status(thm)], ['116', '117'])).
% 2.33/2.57  thf('119', plain,
% 2.33/2.57      (![X32 : $i]:
% 2.33/2.57         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.33/2.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.33/2.57  thf('120', plain,
% 2.33/2.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf(t22_pre_topc, axiom,
% 2.33/2.57    (![A:$i]:
% 2.33/2.57     ( ( l1_struct_0 @ A ) =>
% 2.33/2.57       ( ![B:$i]:
% 2.33/2.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.33/2.57           ( ( k7_subset_1 @
% 2.33/2.57               ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ 
% 2.33/2.57               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 2.33/2.57             ( B ) ) ) ) ))).
% 2.33/2.57  thf('121', plain,
% 2.33/2.57      (![X36 : $i, X37 : $i]:
% 2.33/2.57         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.33/2.57          | ((k7_subset_1 @ (u1_struct_0 @ X37) @ (k2_struct_0 @ X37) @ 
% 2.33/2.57              (k7_subset_1 @ (u1_struct_0 @ X37) @ (k2_struct_0 @ X37) @ X36))
% 2.33/2.57              = (X36))
% 2.33/2.57          | ~ (l1_struct_0 @ X37))),
% 2.33/2.57      inference('cnf', [status(esa)], [t22_pre_topc])).
% 2.33/2.57  thf('122', plain,
% 2.33/2.57      ((~ (l1_struct_0 @ sk_A)
% 2.33/2.57        | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 2.33/2.57            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 2.33/2.57            = (sk_B)))),
% 2.33/2.57      inference('sup-', [status(thm)], ['120', '121'])).
% 2.33/2.57  thf('123', plain, ((l1_struct_0 @ sk_A)),
% 2.33/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.33/2.57  thf('124', plain,
% 2.33/2.57      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 2.33/2.57         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 2.33/2.57         = (sk_B))),
% 2.33/2.57      inference('demod', [status(thm)], ['122', '123'])).
% 2.33/2.57  thf('125', plain,
% 2.33/2.57      ((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 2.33/2.57          (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 2.33/2.57          = (sk_B))
% 2.33/2.57        | ~ (l1_struct_0 @ sk_A))),
% 2.33/2.57      inference('sup+', [status(thm)], ['119', '124'])).
% 2.33/2.57  thf('126', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i]:
% 2.33/2.57         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 2.33/2.57      inference('sup-', [status(thm)], ['108', '109'])).
% 2.33/2.57  thf('127', plain,
% 2.33/2.57      (![X32 : $i]:
% 2.33/2.57         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.33/2.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.33/2.57  thf('128', plain,
% 2.33/2.57      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 2.33/2.57      inference('clc', [status(thm)], ['66', '67'])).
% 2.33/2.57  thf('129', plain,
% 2.33/2.57      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A))))
% 2.33/2.57        | ~ (l1_struct_0 @ sk_A))),
% 2.33/2.57      inference('sup+', [status(thm)], ['127', '128'])).
% 2.33/2.57  thf('130', plain, ((l1_struct_0 @ sk_A)),
% 2.33/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.33/2.57  thf('131', plain,
% 2.33/2.57      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A))))),
% 2.33/2.57      inference('demod', [status(thm)], ['129', '130'])).
% 2.33/2.57  thf('132', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i]:
% 2.33/2.57         ((k4_xboole_0 @ X0 @ X1)
% 2.33/2.57           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 2.33/2.57      inference('sup+', [status(thm)], ['69', '72'])).
% 2.33/2.57  thf('133', plain,
% 2.33/2.57      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 2.33/2.57         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 2.33/2.57      inference('sup+', [status(thm)], ['131', '132'])).
% 2.33/2.57  thf('134', plain, ((l1_struct_0 @ sk_A)),
% 2.33/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.33/2.57  thf('135', plain,
% 2.33/2.57      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 2.33/2.57         (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 2.33/2.57      inference('demod', [status(thm)], ['125', '126', '133', '134'])).
% 2.33/2.57  thf('136', plain,
% 2.33/2.57      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 2.33/2.57         (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 2.33/2.57      inference('demod', [status(thm)], ['125', '126', '133', '134'])).
% 2.33/2.57  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf('138', plain, ((l1_struct_0 @ sk_A)),
% 2.33/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.33/2.57  thf('139', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 2.33/2.57      inference('demod', [status(thm)],
% 2.33/2.57                ['96', '118', '135', '136', '137', '138'])).
% 2.33/2.57  thf('140', plain,
% 2.33/2.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf('141', plain,
% 2.33/2.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.33/2.57         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 2.33/2.57          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 2.33/2.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.33/2.57  thf('142', plain,
% 2.33/2.57      (![X0 : $i]:
% 2.33/2.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.33/2.57           = (k4_xboole_0 @ sk_B @ X0))),
% 2.33/2.57      inference('sup-', [status(thm)], ['140', '141'])).
% 2.33/2.57  thf(t3_boole, axiom,
% 2.33/2.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.33/2.57  thf('143', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 2.33/2.57      inference('cnf', [status(esa)], [t3_boole])).
% 2.33/2.57  thf('144', plain, (((k2_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 2.33/2.57      inference('demod', [status(thm)], ['43', '139', '142', '143'])).
% 2.33/2.57  thf('145', plain,
% 2.33/2.57      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 2.33/2.57         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 2.33/2.57      inference('split', [status(esa)], ['19'])).
% 2.33/2.57  thf('146', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 2.33/2.57      inference('sat_resolution*', [status(thm)], ['20', '39'])).
% 2.33/2.57  thf('147', plain, (((sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 2.33/2.57      inference('simpl_trail', [status(thm)], ['145', '146'])).
% 2.33/2.57  thf('148', plain, ($false),
% 2.33/2.57      inference('simplify_reflect-', [status(thm)], ['144', '147'])).
% 2.33/2.57  
% 2.33/2.57  % SZS output end Refutation
% 2.33/2.57  
% 2.33/2.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
