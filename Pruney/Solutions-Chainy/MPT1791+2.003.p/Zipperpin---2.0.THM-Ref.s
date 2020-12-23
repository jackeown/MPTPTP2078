%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g02FY8gheC

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:45 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 990 expanded)
%              Number of leaves         :   28 ( 287 expanded)
%              Depth                    :   25
%              Number of atoms          : 1843 (15199 expanded)
%              Number of equality atoms :   80 ( 642 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X18 @ X17 ) )
        = ( k5_tmap_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r2_hidden @ X15 @ ( u1_pre_topc @ X16 ) )
      | ( ( u1_pre_topc @ X16 )
        = ( k5_tmap_1 @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X17 ) )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X6 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('37',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('40',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','45'])).

thf('47',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

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

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_tops_2 @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) ) )
      | ( v1_tops_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( ~ ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','45'])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( r1_tarski @ X7 @ ( u1_pre_topc @ X8 ) )
      | ( v1_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['62','64'])).

thf('66',plain,
    ( ( ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','45'])).

thf('70',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_tops_2 @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( u1_pre_topc @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,
    ( ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ( ( u1_pre_topc @ sk_A )
        = ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf(fc5_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ) )).

thf('78',plain,(
    ! [X9: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc5_compts_1])).

thf('79',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X6 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('80',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_tops_2 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['78','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['77','84'])).

thf('86',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_tops_2 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ( v1_tops_2 @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('97',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('98',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( r1_tarski @ X7 @ ( u1_pre_topc @ X8 ) )
      | ( v1_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('99',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
      | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('102',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X6 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('107',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('108',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_tops_2 @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( u1_pre_topc @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','114'])).

thf('116',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','115'])).

thf('117',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( u1_pre_topc @ X16 )
       != ( k5_tmap_1 @ X16 @ X15 ) )
      | ( r2_hidden @ X15 @ ( u1_pre_topc @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('127',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ( v3_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('130',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('135',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('137',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['26','135','136'])).

thf('138',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['24','137'])).

thf('139',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['7','138'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('140',plain,(
    ! [X3: $i] :
      ( ~ ( v1_pre_topc @ X3 )
      | ( X3
        = ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('141',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('143',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('144',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('146',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['141','142','143','151'])).

thf('153',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('154',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
 != ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['26','135'])).

thf('155',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
 != ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['153','154'])).

thf('156',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['152','155'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g02FY8gheC
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 192 iterations in 0.120s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.41/0.59  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.41/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.59  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.59  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.41/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.59  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.41/0.59  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(t106_tmap_1, conjecture,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59           ( ( v3_pre_topc @ B @ A ) <=>
% 0.41/0.59             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.41/0.59               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i]:
% 0.41/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.59            ( l1_pre_topc @ A ) ) =>
% 0.41/0.59          ( ![B:$i]:
% 0.41/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59              ( ( v3_pre_topc @ B @ A ) <=>
% 0.41/0.59                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.41/0.59                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t104_tmap_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.41/0.59             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.59          | ((u1_pre_topc @ (k6_tmap_1 @ X18 @ X17)) = (k5_tmap_1 @ X18 @ X17))
% 0.41/0.59          | ~ (l1_pre_topc @ X18)
% 0.41/0.59          | ~ (v2_pre_topc @ X18)
% 0.41/0.59          | (v2_struct_0 @ X18))),
% 0.41/0.59      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.59  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.41/0.59  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('clc', [status(thm)], ['5', '6'])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.59      inference('split', [status(esa)], ['8'])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(d5_pre_topc, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59           ( ( v3_pre_topc @ B @ A ) <=>
% 0.41/0.59             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X4 : $i, X5 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.41/0.59          | ~ (v3_pre_topc @ X4 @ X5)
% 0.41/0.59          | (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.41/0.59          | ~ (l1_pre_topc @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.41/0.59        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.59  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.41/0.59        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.41/0.59         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['9', '14'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t103_tmap_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.41/0.59             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.59          | ~ (r2_hidden @ X15 @ (u1_pre_topc @ X16))
% 0.41/0.59          | ((u1_pre_topc @ X16) = (k5_tmap_1 @ X16 @ X15))
% 0.41/0.59          | ~ (l1_pre_topc @ X16)
% 0.41/0.59          | ~ (v2_pre_topc @ X16)
% 0.41/0.59          | (v2_struct_0 @ X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.41/0.59  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.41/0.59        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('clc', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['15', '23'])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (~
% 0.41/0.59       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.41/0.59       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.59      inference('split', [status(esa)], ['25'])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('clc', [status(thm)], ['5', '6'])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.59          | ((u1_struct_0 @ (k6_tmap_1 @ X18 @ X17)) = (u1_struct_0 @ X18))
% 0.41/0.59          | ~ (l1_pre_topc @ X18)
% 0.41/0.59          | ~ (v2_pre_topc @ X18)
% 0.41/0.59          | (v2_struct_0 @ X18))),
% 0.41/0.59      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.41/0.59  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.41/0.59  thf(dt_u1_pre_topc, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( m1_subset_1 @
% 0.41/0.59         ( u1_pre_topc @ A ) @ 
% 0.41/0.59         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X6 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (u1_pre_topc @ X6) @ 
% 0.41/0.59           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6))))
% 0.41/0.59          | ~ (l1_pre_topc @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.59        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['35', '36'])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(dt_k6_tmap_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.59         ( l1_pre_topc @ A ) & 
% 0.41/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.59       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.41/0.59         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.41/0.59         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (![X13 : $i, X14 : $i]:
% 0.41/0.59         (~ (l1_pre_topc @ X13)
% 0.41/0.59          | ~ (v2_pre_topc @ X13)
% 0.41/0.59          | (v2_struct_0 @ X13)
% 0.41/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.59          | (l1_pre_topc @ (k6_tmap_1 @ X13 @ X14)))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59        | (v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.59  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.41/0.59  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('45', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('clc', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf('46', plain,
% 0.41/0.59      ((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.59      inference('demod', [status(thm)], ['37', '45'])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('split', [status(esa)], ['8'])).
% 0.41/0.59  thf(t32_compts_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( ( v1_tops_2 @ B @ A ) & 
% 0.41/0.59             ( m1_subset_1 @
% 0.41/0.59               B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) <=>
% 0.41/0.59           ( ( v1_tops_2 @
% 0.41/0.59               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.41/0.59             ( m1_subset_1 @
% 0.41/0.59               B @ 
% 0.41/0.59               ( k1_zfmisc_1 @
% 0.41/0.59                 ( k1_zfmisc_1 @
% 0.41/0.59                   ( u1_struct_0 @
% 0.41/0.59                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]:
% 0.41/0.59         (~ (v1_tops_2 @ X10 @ 
% 0.41/0.59             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.41/0.59          | ~ (m1_subset_1 @ X10 @ 
% 0.41/0.59               (k1_zfmisc_1 @ 
% 0.41/0.59                (k1_zfmisc_1 @ 
% 0.41/0.59                 (u1_struct_0 @ 
% 0.41/0.59                  (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))))))
% 0.41/0.59          | (v1_tops_2 @ X10 @ X11)
% 0.41/0.59          | ~ (l1_pre_topc @ X11)
% 0.41/0.59          | ~ (v2_pre_topc @ X11)
% 0.41/0.59          | (v2_struct_0 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          (~ (m1_subset_1 @ X0 @ 
% 0.41/0.59              (k1_zfmisc_1 @ 
% 0.41/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.41/0.59           | (v2_struct_0 @ sk_A)
% 0.41/0.59           | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59           | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59           | (v1_tops_2 @ X0 @ sk_A)
% 0.41/0.59           | ~ (v1_tops_2 @ X0 @ 
% 0.41/0.59                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.41/0.59  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('split', [status(esa)], ['8'])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          (~ (m1_subset_1 @ X0 @ 
% 0.41/0.59              (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.59           | (v2_struct_0 @ sk_A)
% 0.41/0.59           | (v1_tops_2 @ X0 @ sk_A)
% 0.41/0.59           | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.41/0.59  thf('55', plain,
% 0.41/0.59      (((~ (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59            (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59         | (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ sk_A)
% 0.41/0.59         | (v2_struct_0 @ sk_A)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['46', '54'])).
% 0.41/0.59  thf('56', plain,
% 0.41/0.59      ((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.59      inference('demod', [status(thm)], ['37', '45'])).
% 0.41/0.59  thf('57', plain,
% 0.41/0.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.41/0.59  thf(t78_tops_2, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @
% 0.41/0.59             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.59           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X7 @ 
% 0.41/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.41/0.59          | ~ (r1_tarski @ X7 @ (u1_pre_topc @ X8))
% 0.41/0.59          | (v1_tops_2 @ X7 @ X8)
% 0.41/0.59          | ~ (l1_pre_topc @ X8))),
% 0.41/0.59      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.41/0.59  thf('59', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X0 @ 
% 0.41/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.59          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59          | (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.59  thf('60', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('clc', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf('61', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X0 @ 
% 0.41/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.59          | (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['59', '60'])).
% 0.41/0.59  thf('62', plain,
% 0.41/0.59      ((~ (r1_tarski @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59           (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59        | (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59           (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['56', '61'])).
% 0.41/0.59  thf(d10_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('63', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('64', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.59      inference('simplify', [status(thm)], ['63'])).
% 0.41/0.59  thf('65', plain,
% 0.41/0.59      ((v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59        (k6_tmap_1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['62', '64'])).
% 0.41/0.59  thf('66', plain,
% 0.41/0.59      ((((v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ sk_A)
% 0.41/0.59         | (v2_struct_0 @ sk_A)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['55', '65'])).
% 0.41/0.59  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('68', plain,
% 0.41/0.59      (((v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ sk_A))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('clc', [status(thm)], ['66', '67'])).
% 0.41/0.59  thf('69', plain,
% 0.41/0.59      ((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.59      inference('demod', [status(thm)], ['37', '45'])).
% 0.41/0.59  thf('70', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X7 @ 
% 0.41/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.41/0.59          | ~ (v1_tops_2 @ X7 @ X8)
% 0.41/0.59          | (r1_tarski @ X7 @ (u1_pre_topc @ X8))
% 0.41/0.59          | ~ (l1_pre_topc @ X8))),
% 0.41/0.59      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.41/0.59  thf('71', plain,
% 0.41/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | (r1_tarski @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59           (u1_pre_topc @ sk_A))
% 0.41/0.59        | ~ (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['69', '70'])).
% 0.41/0.59  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('73', plain,
% 0.41/0.59      (((r1_tarski @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59         (u1_pre_topc @ sk_A))
% 0.41/0.59        | ~ (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['71', '72'])).
% 0.41/0.59  thf('74', plain,
% 0.41/0.59      (((r1_tarski @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59         (u1_pre_topc @ sk_A)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['68', '73'])).
% 0.41/0.59  thf('75', plain,
% 0.41/0.59      (![X0 : $i, X2 : $i]:
% 0.41/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('76', plain,
% 0.41/0.59      (((~ (r1_tarski @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.59            (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59         | ((u1_pre_topc @ sk_A) = (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.41/0.59  thf('77', plain,
% 0.41/0.59      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('split', [status(esa)], ['8'])).
% 0.41/0.59  thf(fc5_compts_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ))).
% 0.41/0.59  thf('78', plain,
% 0.41/0.59      (![X9 : $i]:
% 0.41/0.59         ((v1_tops_2 @ (u1_pre_topc @ X9) @ X9) | ~ (l1_pre_topc @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc5_compts_1])).
% 0.41/0.59  thf('79', plain,
% 0.41/0.59      (![X6 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (u1_pre_topc @ X6) @ 
% 0.41/0.59           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6))))
% 0.41/0.59          | ~ (l1_pre_topc @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.41/0.59  thf('80', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i]:
% 0.41/0.59         (~ (v1_tops_2 @ X12 @ X11)
% 0.41/0.59          | ~ (m1_subset_1 @ X12 @ 
% 0.41/0.59               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.41/0.59          | (m1_subset_1 @ X12 @ 
% 0.41/0.59             (k1_zfmisc_1 @ 
% 0.41/0.59              (k1_zfmisc_1 @ 
% 0.41/0.59               (u1_struct_0 @ 
% 0.41/0.59                (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))))))
% 0.41/0.59          | ~ (l1_pre_topc @ X11)
% 0.41/0.59          | ~ (v2_pre_topc @ X11)
% 0.41/0.59          | (v2_struct_0 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.41/0.59  thf('81', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (l1_pre_topc @ X0)
% 0.41/0.59          | (v2_struct_0 @ X0)
% 0.41/0.59          | ~ (v2_pre_topc @ X0)
% 0.41/0.59          | ~ (l1_pre_topc @ X0)
% 0.41/0.59          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.41/0.59             (k1_zfmisc_1 @ 
% 0.41/0.59              (k1_zfmisc_1 @ 
% 0.41/0.59               (u1_struct_0 @ 
% 0.41/0.59                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.41/0.59          | ~ (v1_tops_2 @ (u1_pre_topc @ X0) @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['79', '80'])).
% 0.41/0.59  thf('82', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.41/0.59          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.41/0.59             (k1_zfmisc_1 @ 
% 0.41/0.59              (k1_zfmisc_1 @ 
% 0.41/0.59               (u1_struct_0 @ 
% 0.41/0.59                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.41/0.59          | ~ (v2_pre_topc @ X0)
% 0.41/0.59          | (v2_struct_0 @ X0)
% 0.41/0.59          | ~ (l1_pre_topc @ X0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['81'])).
% 0.41/0.59  thf('83', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (l1_pre_topc @ X0)
% 0.41/0.59          | ~ (l1_pre_topc @ X0)
% 0.41/0.59          | (v2_struct_0 @ X0)
% 0.41/0.59          | ~ (v2_pre_topc @ X0)
% 0.41/0.59          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.41/0.59             (k1_zfmisc_1 @ 
% 0.41/0.59              (k1_zfmisc_1 @ 
% 0.41/0.59               (u1_struct_0 @ 
% 0.41/0.59                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['78', '82'])).
% 0.41/0.59  thf('84', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.41/0.59           (k1_zfmisc_1 @ 
% 0.41/0.59            (k1_zfmisc_1 @ 
% 0.41/0.59             (u1_struct_0 @ 
% 0.41/0.59              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.41/0.59          | ~ (v2_pre_topc @ X0)
% 0.41/0.59          | (v2_struct_0 @ X0)
% 0.41/0.59          | ~ (l1_pre_topc @ X0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['83'])).
% 0.41/0.59  thf('85', plain,
% 0.41/0.59      ((((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.59          (k1_zfmisc_1 @ 
% 0.41/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.41/0.59         | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59         | (v2_struct_0 @ sk_A)
% 0.41/0.59         | ~ (v2_pre_topc @ sk_A)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup+', [status(thm)], ['77', '84'])).
% 0.41/0.59  thf('86', plain,
% 0.41/0.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.41/0.59  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('89', plain,
% 0.41/0.59      ((((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.59          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.59         | (v2_struct_0 @ sk_A)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.41/0.59  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('91', plain,
% 0.41/0.59      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.59         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('clc', [status(thm)], ['89', '90'])).
% 0.41/0.59  thf('92', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i]:
% 0.41/0.59         (~ (v1_tops_2 @ X12 @ X11)
% 0.41/0.59          | ~ (m1_subset_1 @ X12 @ 
% 0.41/0.59               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.41/0.59          | (v1_tops_2 @ X12 @ 
% 0.41/0.59             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.41/0.59          | ~ (l1_pre_topc @ X11)
% 0.41/0.59          | ~ (v2_pre_topc @ X11)
% 0.41/0.59          | (v2_struct_0 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.41/0.59  thf('93', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_A)
% 0.41/0.59         | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59         | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.59            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.41/0.59         | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['91', '92'])).
% 0.41/0.59  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('96', plain,
% 0.41/0.59      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('split', [status(esa)], ['8'])).
% 0.41/0.59  thf('97', plain,
% 0.41/0.59      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.59         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('clc', [status(thm)], ['89', '90'])).
% 0.41/0.59  thf('98', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X7 @ 
% 0.41/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.41/0.59          | ~ (r1_tarski @ X7 @ (u1_pre_topc @ X8))
% 0.41/0.59          | (v1_tops_2 @ X7 @ X8)
% 0.41/0.59          | ~ (l1_pre_topc @ X8))),
% 0.41/0.59      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.41/0.59  thf('99', plain,
% 0.41/0.59      (((~ (l1_pre_topc @ sk_A)
% 0.41/0.59         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.41/0.59         | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.41/0.59  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('101', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.59      inference('simplify', [status(thm)], ['63'])).
% 0.41/0.59  thf('102', plain,
% 0.41/0.59      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.41/0.59  thf('103', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_A)
% 0.41/0.59         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['93', '94', '95', '96', '102'])).
% 0.41/0.59  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('105', plain,
% 0.41/0.59      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('clc', [status(thm)], ['103', '104'])).
% 0.41/0.59  thf('106', plain,
% 0.41/0.59      (![X6 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (u1_pre_topc @ X6) @ 
% 0.41/0.59           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6))))
% 0.41/0.59          | ~ (l1_pre_topc @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.41/0.59  thf('107', plain,
% 0.41/0.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.41/0.59  thf('108', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X7 @ 
% 0.41/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.41/0.59          | ~ (v1_tops_2 @ X7 @ X8)
% 0.41/0.59          | (r1_tarski @ X7 @ (u1_pre_topc @ X8))
% 0.41/0.59          | ~ (l1_pre_topc @ X8))),
% 0.41/0.59      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.41/0.59  thf('109', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X0 @ 
% 0.41/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.59          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59          | (r1_tarski @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59          | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['107', '108'])).
% 0.41/0.59  thf('110', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('clc', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf('111', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X0 @ 
% 0.41/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.59          | (r1_tarski @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59          | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['109', '110'])).
% 0.41/0.59  thf('112', plain,
% 0.41/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59        | (r1_tarski @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.59           (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['106', '111'])).
% 0.41/0.59  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('114', plain,
% 0.41/0.59      ((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59        | (r1_tarski @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.59           (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['112', '113'])).
% 0.41/0.59  thf('115', plain,
% 0.41/0.59      (((r1_tarski @ (u1_pre_topc @ sk_A) @ 
% 0.41/0.59         (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['105', '114'])).
% 0.41/0.59  thf('116', plain,
% 0.41/0.59      ((((u1_pre_topc @ sk_A) = (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['76', '115'])).
% 0.41/0.59  thf('117', plain,
% 0.41/0.59      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup+', [status(thm)], ['27', '116'])).
% 0.41/0.59  thf('118', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('119', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.59          | ((u1_pre_topc @ X16) != (k5_tmap_1 @ X16 @ X15))
% 0.41/0.59          | (r2_hidden @ X15 @ (u1_pre_topc @ X16))
% 0.41/0.59          | ~ (l1_pre_topc @ X16)
% 0.41/0.59          | ~ (v2_pre_topc @ X16)
% 0.41/0.59          | (v2_struct_0 @ X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.41/0.59  thf('120', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.41/0.59        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['118', '119'])).
% 0.41/0.59  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('123', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.41/0.59        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.41/0.59  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('125', plain,
% 0.41/0.59      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['123', '124'])).
% 0.41/0.59  thf('126', plain,
% 0.41/0.59      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.41/0.59         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['117', '125'])).
% 0.41/0.59  thf('127', plain,
% 0.41/0.59      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['126'])).
% 0.41/0.59  thf('128', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('129', plain,
% 0.41/0.59      (![X4 : $i, X5 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.41/0.59          | ~ (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.41/0.59          | (v3_pre_topc @ X4 @ X5)
% 0.41/0.59          | ~ (l1_pre_topc @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.41/0.59  thf('130', plain,
% 0.41/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | (v3_pre_topc @ sk_B @ sk_A)
% 0.41/0.59        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['128', '129'])).
% 0.41/0.59  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('132', plain,
% 0.41/0.59      (((v3_pre_topc @ sk_B @ sk_A)
% 0.41/0.59        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['130', '131'])).
% 0.41/0.59  thf('133', plain,
% 0.41/0.59      (((v3_pre_topc @ sk_B @ sk_A))
% 0.41/0.59         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['127', '132'])).
% 0.41/0.59  thf('134', plain,
% 0.41/0.59      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.59      inference('split', [status(esa)], ['25'])).
% 0.41/0.59  thf('135', plain,
% 0.41/0.59      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.41/0.59       ~
% 0.41/0.59       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          = (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['133', '134'])).
% 0.41/0.59  thf('136', plain,
% 0.41/0.59      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.41/0.59       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          = (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('split', [status(esa)], ['8'])).
% 0.41/0.59  thf('137', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['26', '135', '136'])).
% 0.41/0.59  thf('138', plain, (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['24', '137'])).
% 0.41/0.59  thf('139', plain,
% 0.41/0.59      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['7', '138'])).
% 0.41/0.59  thf(abstractness_v1_pre_topc, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ( v1_pre_topc @ A ) =>
% 0.41/0.59         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.41/0.59  thf('140', plain,
% 0.41/0.59      (![X3 : $i]:
% 0.41/0.59         (~ (v1_pre_topc @ X3)
% 0.41/0.59          | ((X3) = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.41/0.59          | ~ (l1_pre_topc @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.41/0.59  thf('141', plain,
% 0.41/0.59      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.41/0.59          = (g1_pre_topc @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.41/0.59             (u1_pre_topc @ sk_A)))
% 0.41/0.59        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['139', '140'])).
% 0.41/0.59  thf('142', plain,
% 0.41/0.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.41/0.59  thf('143', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('clc', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf('144', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('145', plain,
% 0.41/0.59      (![X13 : $i, X14 : $i]:
% 0.41/0.59         (~ (l1_pre_topc @ X13)
% 0.41/0.59          | ~ (v2_pre_topc @ X13)
% 0.41/0.59          | (v2_struct_0 @ X13)
% 0.41/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.59          | (v1_pre_topc @ (k6_tmap_1 @ X13 @ X14)))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.41/0.59  thf('146', plain,
% 0.41/0.59      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.41/0.59        | (v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['144', '145'])).
% 0.41/0.59  thf('147', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('149', plain,
% 0.41/0.59      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.41/0.59  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('151', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('clc', [status(thm)], ['149', '150'])).
% 0.41/0.59  thf('152', plain,
% 0.41/0.59      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.41/0.59         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['141', '142', '143', '151'])).
% 0.41/0.59  thf('153', plain,
% 0.41/0.59      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.41/0.59         <= (~
% 0.41/0.59             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.41/0.59      inference('split', [status(esa)], ['25'])).
% 0.41/0.59  thf('154', plain,
% 0.41/0.59      (~
% 0.41/0.59       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59          = (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['26', '135'])).
% 0.41/0.59  thf('155', plain,
% 0.41/0.59      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.41/0.59         != (k6_tmap_1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['153', '154'])).
% 0.41/0.59  thf('156', plain, ($false),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['152', '155'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
