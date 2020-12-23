%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j0jDVeWnXC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:48 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 270 expanded)
%              Number of leaves         :   35 (  89 expanded)
%              Depth                    :   20
%              Number of atoms          : 1384 (3877 expanded)
%              Number of equality atoms :   56 ( 161 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ X27 @ ( u1_pre_topc @ X28 ) )
      | ( ( u1_pre_topc @ X28 )
        = ( k5_tmap_1 @ X28 @ X27 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
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
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k6_tmap_1 @ X22 @ X21 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( k5_tmap_1 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf('28',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r2_hidden @ X25 @ ( k5_tmap_1 @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t102_tmap_1])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_B_1 @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X30 @ X29 ) )
        = ( k5_tmap_1 @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(fc5_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ) )).

thf('48',plain,(
    ! [X13: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc5_compts_1])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('50',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_tops_2 @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) ) ) ) )
      | ( v1_tops_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('59',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('60',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['57','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ sk_A )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','68'])).

thf('70',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('71',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X30 @ X29 ) )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('81',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('83',plain,(
    m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(t25_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X20 ) ) ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('85',plain,(
    ! [X17: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('86',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['71','90'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('92',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( u1_pre_topc @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
        | ( m1_subset_1 @ X0 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','93'])).

thf('95',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','94'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('96',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ( v3_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ sk_B_1 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf(fc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('104',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_pre_topc @ X12 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_pre_topc])).

thf('105',plain,
    ( ( ( v3_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('110',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j0jDVeWnXC
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:12:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 285 iterations in 0.224s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.45/0.66  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.45/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.66  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.45/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.66  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.45/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.66  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.66  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.45/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.66  thf(t106_tmap_1, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.66             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.45/0.66               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.66            ( l1_pre_topc @ A ) ) =>
% 0.45/0.66          ( ![B:$i]:
% 0.45/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66              ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.66                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.45/0.66                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66          != (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (~
% 0.45/0.66       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.45/0.66       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66          = (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['2'])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(d5_pre_topc, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.66             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X9 : $i, X10 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.66          | ~ (v3_pre_topc @ X9 @ X10)
% 0.45/0.66          | (r2_hidden @ X9 @ (u1_pre_topc @ X10))
% 0.45/0.66          | ~ (l1_pre_topc @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.45/0.66        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.45/0.66        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))
% 0.45/0.66         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '8'])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t103_tmap_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.45/0.66             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X27 : $i, X28 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.45/0.66          | ~ (r2_hidden @ X27 @ (u1_pre_topc @ X28))
% 0.45/0.66          | ((u1_pre_topc @ X28) = (k5_tmap_1 @ X28 @ X27))
% 0.45/0.66          | ~ (l1_pre_topc @ X28)
% 0.45/0.66          | ~ (v2_pre_topc @ X28)
% 0.45/0.66          | (v2_struct_0 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.45/0.66  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      ((~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.45/0.66        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('clc', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1)))
% 0.45/0.66         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(d9_tmap_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( k6_tmap_1 @ A @ B ) =
% 0.45/0.66             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X21 : $i, X22 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.45/0.66          | ((k6_tmap_1 @ X22 @ X21)
% 0.45/0.66              = (g1_pre_topc @ (u1_struct_0 @ X22) @ (k5_tmap_1 @ X22 @ X21)))
% 0.45/0.66          | ~ (l1_pre_topc @ X22)
% 0.45/0.66          | ~ (v2_pre_topc @ X22)
% 0.45/0.66          | (v2_struct_0 @ X22))),
% 0.45/0.66      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.45/0.66            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.66  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | ((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.45/0.66            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.66  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.45/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('clc', [status(thm)], ['24', '25'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      ((((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.45/0.66          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.45/0.66         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['18', '26'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66          != (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.45/0.66         <= (~
% 0.45/0.66             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      ((((k6_tmap_1 @ sk_A @ sk_B_1) != (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.45/0.66         <= (~
% 0.45/0.66             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))) & 
% 0.45/0.66             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.45/0.66       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('simplify', [status(thm)], ['29'])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.45/0.66       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('split', [status(esa)], ['2'])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t102_tmap_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (![X25 : $i, X26 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.66          | (r2_hidden @ X25 @ (k5_tmap_1 @ X26 @ X25))
% 0.45/0.66          | ~ (l1_pre_topc @ X26)
% 0.45/0.66          | ~ (v2_pre_topc @ X26)
% 0.45/0.66          | (v2_struct_0 @ X26))),
% 0.45/0.66      inference('cnf', [status(esa)], [t102_tmap_1])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | (r2_hidden @ sk_B_1 @ (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.66  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | (r2_hidden @ sk_B_1 @ (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.45/0.66  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('39', plain, ((r2_hidden @ sk_B_1 @ (k5_tmap_1 @ sk_A @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['37', '38'])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t104_tmap_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.45/0.66             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.45/0.66          | ((u1_pre_topc @ (k6_tmap_1 @ X30 @ X29)) = (k5_tmap_1 @ X30 @ X29))
% 0.45/0.66          | ~ (l1_pre_topc @ X30)
% 0.45/0.66          | ~ (v2_pre_topc @ X30)
% 0.45/0.66          | (v2_struct_0 @ X30))),
% 0.45/0.66      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66            = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.66  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66            = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.45/0.66  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66         = (k5_tmap_1 @ sk_A @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['45', '46'])).
% 0.45/0.66  thf(fc5_compts_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ))).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X13 : $i]:
% 0.45/0.66         ((v1_tops_2 @ (u1_pre_topc @ X13) @ X13) | ~ (l1_pre_topc @ X13))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc5_compts_1])).
% 0.45/0.66  thf(dt_u1_pre_topc, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( m1_subset_1 @
% 0.45/0.66         ( u1_pre_topc @ A ) @ 
% 0.45/0.66         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X11 : $i]:
% 0.45/0.66         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.45/0.66           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.45/0.66          | ~ (l1_pre_topc @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66          = (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('split', [status(esa)], ['2'])).
% 0.45/0.66  thf(t32_compts_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( v1_tops_2 @ B @ A ) & 
% 0.45/0.66             ( m1_subset_1 @
% 0.45/0.66               B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) <=>
% 0.45/0.66           ( ( v1_tops_2 @
% 0.45/0.66               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.45/0.66             ( m1_subset_1 @
% 0.45/0.66               B @ 
% 0.45/0.66               ( k1_zfmisc_1 @
% 0.45/0.66                 ( k1_zfmisc_1 @
% 0.45/0.66                   ( u1_struct_0 @
% 0.45/0.66                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i]:
% 0.45/0.66         (~ (v1_tops_2 @ X14 @ 
% 0.45/0.66             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.45/0.66          | ~ (m1_subset_1 @ X14 @ 
% 0.45/0.66               (k1_zfmisc_1 @ 
% 0.45/0.66                (k1_zfmisc_1 @ 
% 0.45/0.66                 (u1_struct_0 @ 
% 0.45/0.66                  (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15))))))
% 0.45/0.66          | (v1_tops_2 @ X14 @ X15)
% 0.45/0.66          | ~ (l1_pre_topc @ X15)
% 0.45/0.66          | ~ (v2_pre_topc @ X15)
% 0.45/0.66          | (v2_struct_0 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.45/0.66  thf('52', plain,
% 0.45/0.66      ((![X0 : $i]:
% 0.45/0.66          (~ (m1_subset_1 @ X0 @ 
% 0.45/0.66              (k1_zfmisc_1 @ 
% 0.45/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))))
% 0.45/0.66           | (v2_struct_0 @ sk_A)
% 0.45/0.66           | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66           | ~ (l1_pre_topc @ sk_A)
% 0.45/0.66           | (v1_tops_2 @ X0 @ sk_A)
% 0.45/0.66           | ~ (v1_tops_2 @ X0 @ 
% 0.45/0.66                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.66  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('55', plain,
% 0.45/0.66      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66          = (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('split', [status(esa)], ['2'])).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      ((![X0 : $i]:
% 0.45/0.66          (~ (m1_subset_1 @ X0 @ 
% 0.45/0.66              (k1_zfmisc_1 @ 
% 0.45/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))))
% 0.45/0.66           | (v2_struct_0 @ sk_A)
% 0.45/0.66           | (v1_tops_2 @ X0 @ sk_A)
% 0.45/0.66           | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_1))))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (((~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66         | ~ (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.45/0.66              (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66         | (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ sk_A)
% 0.45/0.66         | (v2_struct_0 @ sk_A)))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['49', '56'])).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(dt_k6_tmap_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.66         ( l1_pre_topc @ A ) & 
% 0.45/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.66       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.66         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.66         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      (![X23 : $i, X24 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ X23)
% 0.45/0.66          | ~ (v2_pre_topc @ X23)
% 0.45/0.66          | (v2_struct_0 @ X23)
% 0.45/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.45/0.66          | (l1_pre_topc @ (k6_tmap_1 @ X23 @ X24)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.45/0.66  thf('60', plain,
% 0.45/0.66      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66        | (v2_struct_0 @ sk_A)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.66  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('63', plain,
% 0.45/0.66      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.45/0.66  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('65', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['63', '64'])).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (((~ (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.45/0.66            (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66         | (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ sk_A)
% 0.45/0.66         | (v2_struct_0 @ sk_A)))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('demod', [status(thm)], ['57', '65'])).
% 0.45/0.66  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('68', plain,
% 0.45/0.66      ((((v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ sk_A)
% 0.45/0.66         | ~ (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.45/0.66              (k6_tmap_1 @ sk_A @ sk_B_1))))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('clc', [status(thm)], ['66', '67'])).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      (((~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66         | (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ sk_A)))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['48', '68'])).
% 0.45/0.66  thf('70', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['63', '64'])).
% 0.45/0.66  thf('71', plain,
% 0.45/0.66      (((v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ sk_A))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('demod', [status(thm)], ['69', '70'])).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.45/0.66          | ((u1_struct_0 @ (k6_tmap_1 @ X30 @ X29)) = (u1_struct_0 @ X30))
% 0.45/0.66          | ~ (l1_pre_topc @ X30)
% 0.45/0.66          | ~ (v2_pre_topc @ X30)
% 0.45/0.66          | (v2_struct_0 @ X30))),
% 0.45/0.66      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.66  thf('74', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.66  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('77', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.45/0.66  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('79', plain,
% 0.45/0.66      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('clc', [status(thm)], ['77', '78'])).
% 0.45/0.66  thf('80', plain,
% 0.45/0.66      (![X11 : $i]:
% 0.45/0.66         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.45/0.66           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.45/0.66          | ~ (l1_pre_topc @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.45/0.66  thf('81', plain,
% 0.45/0.66      (((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.45/0.66         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.66        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['79', '80'])).
% 0.45/0.66  thf('82', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['63', '64'])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      ((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('demod', [status(thm)], ['81', '82'])).
% 0.45/0.66  thf(t25_yellow_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @
% 0.45/0.66             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.66           ( ( v1_tops_2 @ B @ A ) <=>
% 0.45/0.66             ( m1_subset_1 @
% 0.45/0.66               B @ 
% 0.45/0.66               ( k1_zfmisc_1 @
% 0.45/0.66                 ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X19 @ 
% 0.45/0.66             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.45/0.66          | ~ (v1_tops_2 @ X19 @ X20)
% 0.45/0.66          | (m1_subset_1 @ X19 @ 
% 0.45/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ X20)))))
% 0.45/0.66          | ~ (l1_pre_topc @ X20)
% 0.45/0.66          | ~ (v2_pre_topc @ X20))),
% 0.45/0.66      inference('cnf', [status(esa)], [t25_yellow_1])).
% 0.45/0.66  thf(t1_yellow_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.45/0.66       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.66  thf('85', plain,
% 0.45/0.66      (![X17 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X17)) = (X17))),
% 0.45/0.66      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X19 @ 
% 0.45/0.66             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.45/0.66          | ~ (v1_tops_2 @ X19 @ X20)
% 0.45/0.66          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_pre_topc @ X20)))
% 0.45/0.66          | ~ (l1_pre_topc @ X20)
% 0.45/0.66          | ~ (v2_pre_topc @ X20))),
% 0.45/0.66      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.66  thf('87', plain,
% 0.45/0.66      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | (m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.45/0.66           (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))
% 0.45/0.66        | ~ (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['83', '86'])).
% 0.45/0.66  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('90', plain,
% 0.45/0.66      (((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.45/0.66         (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))
% 0.45/0.66        | ~ (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.45/0.66  thf('91', plain,
% 0.45/0.66      (((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.45/0.66         (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['71', '90'])).
% 0.45/0.66  thf(t4_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.66       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.66  thf('92', plain,
% 0.45/0.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X6 @ X7)
% 0.45/0.66          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.45/0.66          | (m1_subset_1 @ X6 @ X8))),
% 0.45/0.66      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.66  thf('93', plain,
% 0.45/0.66      ((![X0 : $i]:
% 0.45/0.66          ((m1_subset_1 @ X0 @ (u1_pre_topc @ sk_A))
% 0.45/0.66           | ~ (r2_hidden @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)))))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['91', '92'])).
% 0.45/0.66  thf('94', plain,
% 0.45/0.66      ((![X0 : $i]:
% 0.45/0.66          (~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.45/0.66           | (m1_subset_1 @ X0 @ (u1_pre_topc @ sk_A))))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['47', '93'])).
% 0.45/0.66  thf('95', plain,
% 0.45/0.66      (((m1_subset_1 @ sk_B_1 @ (u1_pre_topc @ sk_A)))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['39', '94'])).
% 0.45/0.66  thf(d2_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_xboole_0 @ A ) =>
% 0.45/0.66         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.45/0.66       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.66         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.66  thf('96', plain,
% 0.45/0.66      (![X3 : $i, X4 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X3 @ X4)
% 0.45/0.66          | (r2_hidden @ X3 @ X4)
% 0.45/0.66          | (v1_xboole_0 @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.66  thf('97', plain,
% 0.45/0.66      ((((v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 0.45/0.66         | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['95', '96'])).
% 0.45/0.66  thf('98', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('99', plain,
% 0.45/0.66      (![X9 : $i, X10 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.66          | ~ (r2_hidden @ X9 @ (u1_pre_topc @ X10))
% 0.45/0.66          | (v3_pre_topc @ X9 @ X10)
% 0.45/0.66          | ~ (l1_pre_topc @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.66  thf('100', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.45/0.66        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['98', '99'])).
% 0.45/0.66  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('102', plain,
% 0.45/0.66      (((v3_pre_topc @ sk_B_1 @ sk_A)
% 0.45/0.66        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['100', '101'])).
% 0.45/0.66  thf('103', plain,
% 0.45/0.66      ((((v1_xboole_0 @ (u1_pre_topc @ sk_A)) | (v3_pre_topc @ sk_B_1 @ sk_A)))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['97', '102'])).
% 0.45/0.66  thf(fc1_pre_topc, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ~( v1_xboole_0 @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.66  thf('104', plain,
% 0.45/0.66      (![X12 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ (u1_pre_topc @ X12))
% 0.45/0.66          | ~ (l1_pre_topc @ X12)
% 0.45/0.66          | ~ (v2_pre_topc @ X12))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc1_pre_topc])).
% 0.45/0.66  thf('105', plain,
% 0.45/0.66      ((((v3_pre_topc @ sk_B_1 @ sk_A)
% 0.45/0.66         | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66         | ~ (l1_pre_topc @ sk_A)))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['103', '104'])).
% 0.45/0.66  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('108', plain,
% 0.45/0.66      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 0.45/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.45/0.66      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.45/0.66  thf('109', plain,
% 0.45/0.66      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('110', plain,
% 0.45/0.66      (~
% 0.45/0.66       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.66          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.45/0.66       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['108', '109'])).
% 0.45/0.66  thf('111', plain, ($false),
% 0.45/0.66      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '110'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
