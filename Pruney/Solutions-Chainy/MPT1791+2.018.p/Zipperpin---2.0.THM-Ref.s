%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hEdUkHJkMC

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:48 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 364 expanded)
%              Number of leaves         :   28 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          : 1260 (5394 expanded)
%              Number of equality atoms :   50 ( 233 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(t106_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k6_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_tmap_1])).

thf('0',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X3 @ X4 )
      | ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
          <=> ( ( u1_pre_topc @ A )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_hidden @ X19 @ ( u1_pre_topc @ X20 ) )
      | ( ( u1_pre_topc @ X20 )
        = ( k5_tmap_1 @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k6_tmap_1 @ X14 @ X13 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( k5_tmap_1 @ X14 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf('28',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r2_hidden @ X17 @ ( k5_tmap_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t102_tmap_1])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X22 @ X21 ) )
        = ( k5_tmap_1 @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('52',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['49','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X22 @ X21 ) )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','66'])).

thf('68',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t32_compts_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tops_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
        <=> ( ( v1_tops_2 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_tops_2 @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) ) )
      | ( v1_tops_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,
    ( ( ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','75'])).

thf('77',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(fc5_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ) )).

thf('78',plain,(
    ! [X9: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc5_compts_1])).

thf('79',plain,
    ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('81',plain,(
    v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','66'])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('86',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_tops_2 @ X6 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( v3_pre_topc @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('92',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['90','99'])).

thf('101',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','100'])).

thf('102',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hEdUkHJkMC
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.63  % Solved by: fo/fo7.sh
% 0.47/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.63  % done 190 iterations in 0.165s
% 0.47/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.63  % SZS output start Refutation
% 0.47/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.63  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.47/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.63  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.47/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.63  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.47/0.63  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.47/0.63  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.47/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.63  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.47/0.63  thf(t106_tmap_1, conjecture,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ( v3_pre_topc @ B @ A ) <=>
% 0.47/0.63             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.47/0.63               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.63    (~( ![A:$i]:
% 0.47/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.63            ( l1_pre_topc @ A ) ) =>
% 0.47/0.63          ( ![B:$i]:
% 0.47/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63              ( ( v3_pre_topc @ B @ A ) <=>
% 0.47/0.63                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.47/0.63                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.47/0.63    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.47/0.63  thf('0', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('1', plain,
% 0.47/0.63      (~
% 0.47/0.63       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.47/0.63       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('2', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('3', plain,
% 0.47/0.63      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.63      inference('split', [status(esa)], ['2'])).
% 0.47/0.63  thf('4', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(d5_pre_topc, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_pre_topc @ A ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ( v3_pre_topc @ B @ A ) <=>
% 0.47/0.63             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.47/0.63  thf('5', plain,
% 0.47/0.63      (![X3 : $i, X4 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.47/0.63          | ~ (v3_pre_topc @ X3 @ X4)
% 0.47/0.63          | (r2_hidden @ X3 @ (u1_pre_topc @ X4))
% 0.47/0.63          | ~ (l1_pre_topc @ X4))),
% 0.47/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.47/0.63  thf('6', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.47/0.63        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.63  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('8', plain,
% 0.47/0.63      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.47/0.63        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.47/0.63  thf('9', plain,
% 0.47/0.63      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.47/0.63         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['3', '8'])).
% 0.47/0.63  thf('10', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(t103_tmap_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.47/0.63             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.63  thf('11', plain,
% 0.47/0.63      (![X19 : $i, X20 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.47/0.63          | ~ (r2_hidden @ X19 @ (u1_pre_topc @ X20))
% 0.47/0.63          | ((u1_pre_topc @ X20) = (k5_tmap_1 @ X20 @ X19))
% 0.47/0.63          | ~ (l1_pre_topc @ X20)
% 0.47/0.63          | ~ (v2_pre_topc @ X20)
% 0.47/0.63          | (v2_struct_0 @ X20))),
% 0.47/0.63      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.47/0.63  thf('12', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.63  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('15', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.47/0.63  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('17', plain,
% 0.47/0.63      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.47/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('clc', [status(thm)], ['15', '16'])).
% 0.47/0.63  thf('18', plain,
% 0.47/0.63      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.63         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['9', '17'])).
% 0.47/0.63  thf('19', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(d9_tmap_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ( k6_tmap_1 @ A @ B ) =
% 0.47/0.63             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.63  thf('20', plain,
% 0.47/0.63      (![X13 : $i, X14 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.47/0.63          | ((k6_tmap_1 @ X14 @ X13)
% 0.47/0.63              = (g1_pre_topc @ (u1_struct_0 @ X14) @ (k5_tmap_1 @ X14 @ X13)))
% 0.47/0.63          | ~ (l1_pre_topc @ X14)
% 0.47/0.63          | ~ (v2_pre_topc @ X14)
% 0.47/0.63          | (v2_struct_0 @ X14))),
% 0.47/0.63      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.47/0.63  thf('21', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.47/0.63            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.63  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('24', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.47/0.63            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.47/0.63  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('26', plain,
% 0.47/0.63      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.47/0.63         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('clc', [status(thm)], ['24', '25'])).
% 0.47/0.63  thf('27', plain,
% 0.47/0.63      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.47/0.63          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.47/0.63         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['18', '26'])).
% 0.47/0.63  thf('28', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.63         <= (~
% 0.47/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('29', plain,
% 0.47/0.63      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.63         <= (~
% 0.47/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.47/0.63             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.63  thf('30', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.47/0.63       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.63      inference('simplify', [status(thm)], ['29'])).
% 0.47/0.63  thf('31', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.47/0.63       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.63      inference('split', [status(esa)], ['2'])).
% 0.47/0.63  thf('32', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(t102_tmap_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.47/0.63  thf('33', plain,
% 0.47/0.63      (![X17 : $i, X18 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.47/0.63          | (r2_hidden @ X17 @ (k5_tmap_1 @ X18 @ X17))
% 0.47/0.63          | ~ (l1_pre_topc @ X18)
% 0.47/0.63          | ~ (v2_pre_topc @ X18)
% 0.47/0.63          | (v2_struct_0 @ X18))),
% 0.47/0.63      inference('cnf', [status(esa)], [t102_tmap_1])).
% 0.47/0.63  thf('34', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.63  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('37', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.47/0.63  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('39', plain, ((r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.63      inference('clc', [status(thm)], ['37', '38'])).
% 0.47/0.63  thf('40', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(t104_tmap_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.47/0.63             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.63  thf('41', plain,
% 0.47/0.63      (![X21 : $i, X22 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.47/0.63          | ((u1_pre_topc @ (k6_tmap_1 @ X22 @ X21)) = (k5_tmap_1 @ X22 @ X21))
% 0.47/0.63          | ~ (l1_pre_topc @ X22)
% 0.47/0.63          | ~ (v2_pre_topc @ X22)
% 0.47/0.63          | (v2_struct_0 @ X22))),
% 0.47/0.63      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.47/0.63  thf('42', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.63  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('45', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.47/0.63  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('47', plain,
% 0.47/0.63      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.63      inference('clc', [status(thm)], ['45', '46'])).
% 0.47/0.63  thf(dt_u1_pre_topc, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_pre_topc @ A ) =>
% 0.47/0.63       ( m1_subset_1 @
% 0.47/0.63         ( u1_pre_topc @ A ) @ 
% 0.47/0.63         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.47/0.63  thf('48', plain,
% 0.47/0.63      (![X5 : $i]:
% 0.47/0.63         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.47/0.63           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.47/0.63          | ~ (l1_pre_topc @ X5))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.47/0.63  thf('49', plain,
% 0.47/0.63      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.47/0.63         (k1_zfmisc_1 @ 
% 0.47/0.63          (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.47/0.63        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['47', '48'])).
% 0.47/0.63  thf('50', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(dt_k6_tmap_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.63         ( l1_pre_topc @ A ) & 
% 0.47/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.63       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.47/0.63         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.47/0.63         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.47/0.63  thf('51', plain,
% 0.47/0.63      (![X15 : $i, X16 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X15)
% 0.47/0.63          | ~ (v2_pre_topc @ X15)
% 0.47/0.63          | (v2_struct_0 @ X15)
% 0.47/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.63          | (l1_pre_topc @ (k6_tmap_1 @ X15 @ X16)))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.47/0.63  thf('52', plain,
% 0.47/0.63      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.63  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('55', plain,
% 0.47/0.63      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.47/0.63  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('57', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.63      inference('clc', [status(thm)], ['55', '56'])).
% 0.47/0.63  thf('58', plain,
% 0.47/0.63      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['49', '57'])).
% 0.47/0.63  thf('59', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('60', plain,
% 0.47/0.63      (![X21 : $i, X22 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.47/0.63          | ((u1_struct_0 @ (k6_tmap_1 @ X22 @ X21)) = (u1_struct_0 @ X22))
% 0.47/0.63          | ~ (l1_pre_topc @ X22)
% 0.47/0.63          | ~ (v2_pre_topc @ X22)
% 0.47/0.63          | (v2_struct_0 @ X22))),
% 0.47/0.63      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.47/0.63  thf('61', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.47/0.63  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('64', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.47/0.63  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('66', plain,
% 0.47/0.63      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('clc', [status(thm)], ['64', '65'])).
% 0.47/0.63  thf('67', plain,
% 0.47/0.63      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.47/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['58', '66'])).
% 0.47/0.63  thf('68', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('split', [status(esa)], ['2'])).
% 0.47/0.63  thf(t32_compts_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( ( v1_tops_2 @ B @ A ) & 
% 0.47/0.63             ( m1_subset_1 @
% 0.47/0.63               B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) <=>
% 0.47/0.63           ( ( v1_tops_2 @
% 0.47/0.63               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.47/0.63             ( m1_subset_1 @
% 0.47/0.63               B @ 
% 0.47/0.63               ( k1_zfmisc_1 @
% 0.47/0.63                 ( k1_zfmisc_1 @
% 0.47/0.63                   ( u1_struct_0 @
% 0.47/0.63                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.63  thf('69', plain,
% 0.47/0.63      (![X10 : $i, X11 : $i]:
% 0.47/0.63         (~ (v1_tops_2 @ X10 @ 
% 0.47/0.63             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.47/0.63          | ~ (m1_subset_1 @ X10 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (k1_zfmisc_1 @ 
% 0.47/0.63                 (u1_struct_0 @ 
% 0.47/0.63                  (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))))))
% 0.47/0.63          | (v1_tops_2 @ X10 @ X11)
% 0.47/0.63          | ~ (l1_pre_topc @ X11)
% 0.47/0.63          | ~ (v2_pre_topc @ X11)
% 0.47/0.63          | (v2_struct_0 @ X11))),
% 0.47/0.63      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.47/0.63  thf('70', plain,
% 0.47/0.63      ((![X0 : $i]:
% 0.47/0.63          (~ (m1_subset_1 @ X0 @ 
% 0.47/0.63              (k1_zfmisc_1 @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.47/0.63           | (v2_struct_0 @ sk_A)
% 0.47/0.63           | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63           | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63           | (v1_tops_2 @ X0 @ sk_A)
% 0.47/0.63           | ~ (v1_tops_2 @ X0 @ 
% 0.47/0.63                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.47/0.63  thf('71', plain,
% 0.47/0.63      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('clc', [status(thm)], ['64', '65'])).
% 0.47/0.63  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('74', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('split', [status(esa)], ['2'])).
% 0.47/0.63  thf('75', plain,
% 0.47/0.63      ((![X0 : $i]:
% 0.47/0.63          (~ (m1_subset_1 @ X0 @ 
% 0.47/0.63              (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63           | (v2_struct_0 @ sk_A)
% 0.47/0.63           | (v1_tops_2 @ X0 @ sk_A)
% 0.47/0.63           | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('demod', [status(thm)], ['70', '71', '72', '73', '74'])).
% 0.47/0.63  thf('76', plain,
% 0.47/0.63      (((~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63         | (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 0.47/0.63         | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['67', '75'])).
% 0.47/0.63  thf('77', plain,
% 0.47/0.63      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.63      inference('clc', [status(thm)], ['45', '46'])).
% 0.47/0.63  thf(fc5_compts_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_pre_topc @ A ) => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ))).
% 0.47/0.63  thf('78', plain,
% 0.47/0.63      (![X9 : $i]:
% 0.47/0.63         ((v1_tops_2 @ (u1_pre_topc @ X9) @ X9) | ~ (l1_pre_topc @ X9))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc5_compts_1])).
% 0.47/0.63  thf('79', plain,
% 0.47/0.63      (((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['77', '78'])).
% 0.47/0.63  thf('80', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.63      inference('clc', [status(thm)], ['55', '56'])).
% 0.47/0.63  thf('81', plain,
% 0.47/0.63      ((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.63      inference('demod', [status(thm)], ['79', '80'])).
% 0.47/0.63  thf('82', plain,
% 0.47/0.63      ((((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('demod', [status(thm)], ['76', '81'])).
% 0.47/0.63  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('84', plain,
% 0.47/0.63      (((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('clc', [status(thm)], ['82', '83'])).
% 0.47/0.63  thf('85', plain,
% 0.47/0.63      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.47/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['58', '66'])).
% 0.47/0.63  thf(d1_tops_2, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_pre_topc @ A ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @
% 0.47/0.63             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.63           ( ( v1_tops_2 @ B @ A ) <=>
% 0.47/0.63             ( ![C:$i]:
% 0.47/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.47/0.63  thf('86', plain,
% 0.47/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X6 @ 
% 0.47/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.47/0.63          | ~ (v1_tops_2 @ X6 @ X7)
% 0.47/0.63          | ~ (r2_hidden @ X8 @ X6)
% 0.47/0.63          | (v3_pre_topc @ X8 @ X7)
% 0.47/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.47/0.63          | ~ (l1_pre_topc @ X7))),
% 0.47/0.63      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.47/0.63  thf('87', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63          | (v3_pre_topc @ X0 @ sk_A)
% 0.47/0.63          | ~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63          | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['85', '86'])).
% 0.47/0.63  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('89', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63          | (v3_pre_topc @ X0 @ sk_A)
% 0.47/0.63          | ~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63          | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['87', '88'])).
% 0.47/0.63  thf('90', plain,
% 0.47/0.63      ((![X0 : $i]:
% 0.47/0.63          (~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63           | (v3_pre_topc @ X0 @ sk_A)
% 0.47/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['84', '89'])).
% 0.47/0.63  thf('91', plain,
% 0.47/0.63      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.63      inference('clc', [status(thm)], ['45', '46'])).
% 0.47/0.63  thf('92', plain,
% 0.47/0.63      (![X5 : $i]:
% 0.47/0.63         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.47/0.63           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.47/0.63          | ~ (l1_pre_topc @ X5))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.47/0.63  thf(t4_subset, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.47/0.63       ( m1_subset_1 @ A @ C ) ))).
% 0.47/0.63  thf('93', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.47/0.63          | (m1_subset_1 @ X0 @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [t4_subset])).
% 0.47/0.63  thf('94', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X0)
% 0.47/0.63          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.63          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['92', '93'])).
% 0.47/0.63  thf('95', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63          | (m1_subset_1 @ X0 @ 
% 0.47/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.47/0.63          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['91', '94'])).
% 0.47/0.63  thf('96', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.63      inference('clc', [status(thm)], ['55', '56'])).
% 0.47/0.63  thf('97', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63          | (m1_subset_1 @ X0 @ 
% 0.47/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['95', '96'])).
% 0.47/0.63  thf('98', plain,
% 0.47/0.63      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('clc', [status(thm)], ['64', '65'])).
% 0.47/0.63  thf('99', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.63          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['97', '98'])).
% 0.47/0.63  thf('100', plain,
% 0.47/0.63      ((![X0 : $i]:
% 0.47/0.63          ((v3_pre_topc @ X0 @ sk_A)
% 0.47/0.63           | ~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('clc', [status(thm)], ['90', '99'])).
% 0.47/0.63  thf('101', plain,
% 0.47/0.63      (((v3_pre_topc @ sk_B @ sk_A))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['39', '100'])).
% 0.47/0.63  thf('102', plain,
% 0.47/0.63      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('103', plain,
% 0.47/0.63      (~
% 0.47/0.63       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.47/0.63       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['101', '102'])).
% 0.47/0.63  thf('104', plain, ($false),
% 0.47/0.63      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '103'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
