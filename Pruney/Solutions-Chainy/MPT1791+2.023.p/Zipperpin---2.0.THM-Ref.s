%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SdUECcsPBE

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:48 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 380 expanded)
%              Number of leaves         :   35 ( 120 expanded)
%              Depth                    :   19
%              Number of atoms          : 1403 (5601 expanded)
%              Number of equality atoms :   56 ( 226 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ( r2_hidden @ X8 @ ( u1_pre_topc @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r2_hidden @ X25 @ ( u1_pre_topc @ X26 ) )
      | ( ( u1_pre_topc @ X26 )
        = ( k5_tmap_1 @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k6_tmap_1 @ X20 @ X19 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( k5_tmap_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r2_hidden @ X23 @ ( k5_tmap_1 @ X24 @ X23 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
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
    r2_hidden @ sk_B @ ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X28 @ X27 ) )
        = ( k5_tmap_1 @ X28 @ X27 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(fc5_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ) )).

thf('50',plain,(
    ! [X11: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc5_compts_1])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('51',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

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

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_tops_2 @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) ) ) )
      | ( v1_tops_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ X0 )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v1_tops_2 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tops_2 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('59',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ X27 ) )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('80',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('82',plain,(
    m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(t25_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_tops_2 @ X17 @ X18 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X18 ) ) ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('84',plain,(
    ! [X15: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('85',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_tops_2 @ X17 @ X18 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','89'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('91',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( u1_pre_topc @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) )
        | ( m1_subset_1 @ X0 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','92'])).

thf('94',plain,
    ( ( m1_subset_1 @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','93'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('96',plain,
    ( ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X8 @ ( u1_pre_topc @ X9 ) )
      | ( v3_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('104',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','89'])).

thf('105',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('106',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','108'])).

thf('110',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('111',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SdUECcsPBE
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 328 iterations in 0.218s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.68  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.45/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.68  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.68  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.45/0.68  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.68  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.68  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.45/0.68  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.45/0.68  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(t106_tmap_1, conjecture,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.68             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.45/0.68               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i]:
% 0.45/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.68            ( l1_pre_topc @ A ) ) =>
% 0.45/0.68          ( ![B:$i]:
% 0.45/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68              ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.68                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.45/0.68                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (~
% 0.45/0.68       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.68       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.68      inference('split', [status(esa)], ['0'])).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.68      inference('split', [status(esa)], ['2'])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(d5_pre_topc, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_pre_topc @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.68             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.45/0.68          | ~ (v3_pre_topc @ X8 @ X9)
% 0.45/0.68          | (r2_hidden @ X8 @ (u1_pre_topc @ X9))
% 0.45/0.68          | ~ (l1_pre_topc @ X9))),
% 0.45/0.68      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.45/0.68        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.68  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.45/0.68        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.45/0.68         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['3', '8'])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t103_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.45/0.68             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.68          | ~ (r2_hidden @ X25 @ (u1_pre_topc @ X26))
% 0.45/0.68          | ((u1_pre_topc @ X26) = (k5_tmap_1 @ X26 @ X25))
% 0.45/0.68          | ~ (l1_pre_topc @ X26)
% 0.45/0.68          | ~ (v2_pre_topc @ X26)
% 0.45/0.68          | (v2_struct_0 @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.45/0.68  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.45/0.68        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['15', '16'])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.68         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['9', '17'])).
% 0.45/0.68  thf('19', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(d9_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( k6_tmap_1 @ A @ B ) =
% 0.45/0.68             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X19 : $i, X20 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.45/0.68          | ((k6_tmap_1 @ X20 @ X19)
% 0.45/0.68              = (g1_pre_topc @ (u1_struct_0 @ X20) @ (k5_tmap_1 @ X20 @ X19)))
% 0.45/0.68          | ~ (l1_pre_topc @ X20)
% 0.45/0.68          | ~ (v2_pre_topc @ X20)
% 0.45/0.68          | (v2_struct_0 @ X20))),
% 0.45/0.68      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.45/0.68            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.68  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('24', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.45/0.68            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.68  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.45/0.68         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['24', '25'])).
% 0.45/0.68  thf('27', plain,
% 0.45/0.68      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.45/0.68          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.45/0.68         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['18', '26'])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.68         <= (~
% 0.45/0.68             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('split', [status(esa)], ['0'])).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.68         <= (~
% 0.45/0.68             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.45/0.68             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.68  thf('30', plain,
% 0.45/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.68       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.68      inference('simplify', [status(thm)], ['29'])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.68       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.68      inference('split', [status(esa)], ['2'])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t102_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      (![X23 : $i, X24 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.68          | (r2_hidden @ X23 @ (k5_tmap_1 @ X24 @ X23))
% 0.45/0.68          | ~ (l1_pre_topc @ X24)
% 0.45/0.68          | ~ (v2_pre_topc @ X24)
% 0.45/0.68          | (v2_struct_0 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [t102_tmap_1])).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | (r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.68  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.45/0.68  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('39', plain, ((r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['37', '38'])).
% 0.45/0.68  thf('40', plain, ((r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['37', '38'])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t104_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.45/0.68             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      (![X27 : $i, X28 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.45/0.68          | ((u1_pre_topc @ (k6_tmap_1 @ X28 @ X27)) = (k5_tmap_1 @ X28 @ X27))
% 0.45/0.68          | ~ (l1_pre_topc @ X28)
% 0.45/0.68          | ~ (v2_pre_topc @ X28)
% 0.45/0.68          | (v2_struct_0 @ X28))),
% 0.45/0.68      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.68  thf('43', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.68  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('46', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.45/0.68  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('48', plain,
% 0.45/0.68      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['46', '47'])).
% 0.45/0.68  thf('49', plain,
% 0.45/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('split', [status(esa)], ['2'])).
% 0.45/0.68  thf(fc5_compts_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_pre_topc @ A ) => ( v1_tops_2 @ ( u1_pre_topc @ A ) @ A ) ))).
% 0.45/0.68  thf('50', plain,
% 0.45/0.68      (![X11 : $i]:
% 0.45/0.68         ((v1_tops_2 @ (u1_pre_topc @ X11) @ X11) | ~ (l1_pre_topc @ X11))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc5_compts_1])).
% 0.45/0.68  thf(dt_u1_pre_topc, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_pre_topc @ A ) =>
% 0.45/0.68       ( m1_subset_1 @
% 0.45/0.68         ( u1_pre_topc @ A ) @ 
% 0.45/0.68         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.45/0.68  thf('51', plain,
% 0.45/0.68      (![X10 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.45/0.68           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.45/0.68          | ~ (l1_pre_topc @ X10))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.45/0.68  thf(t32_compts_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( ( v1_tops_2 @ B @ A ) & 
% 0.45/0.68             ( m1_subset_1 @
% 0.45/0.68               B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) <=>
% 0.45/0.68           ( ( v1_tops_2 @
% 0.45/0.68               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.45/0.68             ( m1_subset_1 @
% 0.45/0.68               B @ 
% 0.45/0.68               ( k1_zfmisc_1 @
% 0.45/0.68                 ( k1_zfmisc_1 @
% 0.45/0.68                   ( u1_struct_0 @
% 0.45/0.68                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('52', plain,
% 0.45/0.68      (![X12 : $i, X13 : $i]:
% 0.45/0.68         (~ (v1_tops_2 @ X12 @ 
% 0.45/0.68             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.45/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k1_zfmisc_1 @ 
% 0.45/0.68                 (u1_struct_0 @ 
% 0.45/0.68                  (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))))))
% 0.45/0.68          | (v1_tops_2 @ X12 @ X13)
% 0.45/0.68          | ~ (l1_pre_topc @ X13)
% 0.45/0.68          | ~ (v2_pre_topc @ X13)
% 0.45/0.68          | (v2_struct_0 @ X13))),
% 0.45/0.68      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.45/0.68  thf('53', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ 
% 0.45/0.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.68          | (v2_struct_0 @ X0)
% 0.45/0.68          | ~ (v2_pre_topc @ X0)
% 0.45/0.68          | ~ (l1_pre_topc @ X0)
% 0.45/0.68          | (v1_tops_2 @ 
% 0.45/0.68             (u1_pre_topc @ 
% 0.45/0.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.45/0.68             X0)
% 0.45/0.68          | ~ (v1_tops_2 @ 
% 0.45/0.68               (u1_pre_topc @ 
% 0.45/0.68                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.45/0.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.68  thf('54', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ 
% 0.45/0.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.68          | (v1_tops_2 @ 
% 0.45/0.68             (u1_pre_topc @ 
% 0.45/0.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.45/0.68             X0)
% 0.45/0.68          | ~ (l1_pre_topc @ X0)
% 0.45/0.68          | ~ (v2_pre_topc @ X0)
% 0.45/0.68          | (v2_struct_0 @ X0)
% 0.45/0.68          | ~ (l1_pre_topc @ 
% 0.45/0.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['50', '53'])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((v2_struct_0 @ X0)
% 0.45/0.68          | ~ (v2_pre_topc @ X0)
% 0.45/0.68          | ~ (l1_pre_topc @ X0)
% 0.45/0.68          | (v1_tops_2 @ 
% 0.45/0.68             (u1_pre_topc @ 
% 0.45/0.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.45/0.68             X0)
% 0.45/0.68          | ~ (l1_pre_topc @ 
% 0.45/0.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['54'])).
% 0.45/0.68  thf('56', plain,
% 0.45/0.68      (((~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68         | (v1_tops_2 @ 
% 0.45/0.68            (u1_pre_topc @ 
% 0.45/0.68             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.45/0.68            sk_A)
% 0.45/0.68         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68         | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68         | (v2_struct_0 @ sk_A)))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['49', '55'])).
% 0.45/0.68  thf('57', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(dt_k6_tmap_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.68         ( l1_pre_topc @ A ) & 
% 0.45/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.68       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.68         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.68         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.45/0.68  thf('58', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X21)
% 0.45/0.68          | ~ (v2_pre_topc @ X21)
% 0.45/0.68          | (v2_struct_0 @ X21)
% 0.45/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.68          | (l1_pre_topc @ (k6_tmap_1 @ X21 @ X22)))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.45/0.68  thf('59', plain,
% 0.45/0.68      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.68  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('62', plain,
% 0.45/0.68      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.45/0.68  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('64', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['62', '63'])).
% 0.45/0.68  thf('65', plain,
% 0.45/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('split', [status(esa)], ['2'])).
% 0.45/0.68  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('68', plain,
% 0.45/0.68      ((((v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ sk_A)
% 0.45/0.68         | (v2_struct_0 @ sk_A)))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['56', '64', '65', '66', '67'])).
% 0.45/0.68  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('70', plain,
% 0.45/0.68      (((v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ sk_A))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('clc', [status(thm)], ['68', '69'])).
% 0.45/0.68  thf('71', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('72', plain,
% 0.45/0.68      (![X27 : $i, X28 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.45/0.68          | ((u1_struct_0 @ (k6_tmap_1 @ X28 @ X27)) = (u1_struct_0 @ X28))
% 0.45/0.68          | ~ (l1_pre_topc @ X28)
% 0.45/0.68          | ~ (v2_pre_topc @ X28)
% 0.45/0.68          | (v2_struct_0 @ X28))),
% 0.45/0.68      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.68  thf('73', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.68  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('76', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.45/0.68  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('78', plain,
% 0.45/0.68      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['76', '77'])).
% 0.45/0.68  thf('79', plain,
% 0.45/0.68      (![X10 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.45/0.68           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.45/0.68          | ~ (l1_pre_topc @ X10))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.45/0.68  thf('80', plain,
% 0.45/0.68      (((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.45/0.68         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['78', '79'])).
% 0.45/0.68  thf('81', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['62', '63'])).
% 0.45/0.68  thf('82', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.68  thf(t25_yellow_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @
% 0.45/0.68             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.68           ( ( v1_tops_2 @ B @ A ) <=>
% 0.45/0.68             ( m1_subset_1 @
% 0.45/0.68               B @ 
% 0.45/0.68               ( k1_zfmisc_1 @
% 0.45/0.68                 ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('83', plain,
% 0.45/0.68      (![X17 : $i, X18 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X17 @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.45/0.68          | ~ (v1_tops_2 @ X17 @ X18)
% 0.45/0.68          | (m1_subset_1 @ X17 @ 
% 0.45/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ X18)))))
% 0.45/0.68          | ~ (l1_pre_topc @ X18)
% 0.45/0.68          | ~ (v2_pre_topc @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [t25_yellow_1])).
% 0.45/0.68  thf(t1_yellow_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.45/0.68       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.68  thf('84', plain,
% 0.45/0.68      (![X15 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X15)) = (X15))),
% 0.45/0.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.68  thf('85', plain,
% 0.45/0.68      (![X17 : $i, X18 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X17 @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.45/0.68          | ~ (v1_tops_2 @ X17 @ X18)
% 0.45/0.68          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_pre_topc @ X18)))
% 0.45/0.68          | ~ (l1_pre_topc @ X18)
% 0.45/0.68          | ~ (v2_pre_topc @ X18))),
% 0.45/0.68      inference('demod', [status(thm)], ['83', '84'])).
% 0.45/0.68  thf('86', plain,
% 0.45/0.68      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | (m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.45/0.68           (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))
% 0.45/0.68        | ~ (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['82', '85'])).
% 0.45/0.68  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('89', plain,
% 0.45/0.68      (((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.45/0.68         (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))
% 0.45/0.68        | ~ (v1_tops_2 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.45/0.68  thf('90', plain,
% 0.45/0.68      (((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.45/0.68         (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['70', '89'])).
% 0.45/0.68  thf(t4_subset, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.68       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.68  thf('91', plain,
% 0.45/0.68      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X2 @ X3)
% 0.45/0.68          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.45/0.68          | (m1_subset_1 @ X2 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.68  thf('92', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          ((m1_subset_1 @ X0 @ (u1_pre_topc @ sk_A))
% 0.45/0.68           | ~ (r2_hidden @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['90', '91'])).
% 0.45/0.68  thf('93', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          (~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68           | (m1_subset_1 @ X0 @ (u1_pre_topc @ sk_A))))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['48', '92'])).
% 0.45/0.68  thf('94', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['40', '93'])).
% 0.45/0.68  thf(t2_subset, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.68       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.68  thf('95', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((r2_hidden @ X0 @ X1)
% 0.45/0.68          | (v1_xboole_0 @ X1)
% 0.45/0.68          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.68  thf('96', plain,
% 0.45/0.68      ((((v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 0.45/0.68         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['94', '95'])).
% 0.45/0.68  thf('97', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('98', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.45/0.68          | ~ (r2_hidden @ X8 @ (u1_pre_topc @ X9))
% 0.45/0.68          | (v3_pre_topc @ X8 @ X9)
% 0.45/0.68          | ~ (l1_pre_topc @ X9))),
% 0.45/0.68      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.68  thf('99', plain,
% 0.45/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | (v3_pre_topc @ sk_B @ sk_A)
% 0.45/0.68        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['97', '98'])).
% 0.45/0.68  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('101', plain,
% 0.45/0.68      (((v3_pre_topc @ sk_B @ sk_A)
% 0.45/0.68        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['99', '100'])).
% 0.45/0.68  thf('102', plain,
% 0.45/0.68      ((((v1_xboole_0 @ (u1_pre_topc @ sk_A)) | (v3_pre_topc @ sk_B @ sk_A)))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['96', '101'])).
% 0.45/0.68  thf('103', plain,
% 0.45/0.68      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['46', '47'])).
% 0.45/0.68  thf('104', plain,
% 0.45/0.68      (((m1_subset_1 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 0.45/0.68         (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['70', '89'])).
% 0.45/0.68  thf('105', plain,
% 0.45/0.68      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68         (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['103', '104'])).
% 0.45/0.68  thf(t5_subset, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.68          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.68  thf('106', plain,
% 0.45/0.68      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X5 @ X6)
% 0.45/0.68          | ~ (v1_xboole_0 @ X7)
% 0.45/0.68          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.68  thf('107', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          (~ (v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 0.45/0.68           | ~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['105', '106'])).
% 0.45/0.68  thf('108', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          ((v3_pre_topc @ sk_B @ sk_A)
% 0.45/0.68           | ~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['102', '107'])).
% 0.45/0.68  thf('109', plain,
% 0.45/0.68      (((v3_pre_topc @ sk_B @ sk_A))
% 0.45/0.68         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['39', '108'])).
% 0.45/0.68  thf('110', plain,
% 0.45/0.68      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.68      inference('split', [status(esa)], ['0'])).
% 0.45/0.68  thf('111', plain,
% 0.45/0.68      (~
% 0.45/0.68       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.68          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.68       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['109', '110'])).
% 0.45/0.68  thf('112', plain, ($false),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '111'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.51/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
