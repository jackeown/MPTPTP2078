%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.52eycSYShv

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:34 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  526 (1711303 expanded)
%              Number of leaves         :   57 (505228 expanded)
%              Depth                    :  183
%              Number of atoms          : 10660 (53162170 expanded)
%              Number of equality atoms :  370 (893319 expanded)
%              Maximal formula depth    :   28 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(k1_waybel_2_type,type,(
    k1_waybel_2: $i > $i > $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k4_yellow_2_type,type,(
    k4_yellow_2: $i > $i > $i )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v10_waybel_0_type,type,(
    v10_waybel_0: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(t35_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v1_compts_1 @ A )
        & ( l1_waybel_9 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v4_orders_2 @ C )
                & ( v7_waybel_0 @ C )
                & ( l1_waybel_0 @ C @ A ) )
             => ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) )
                  & ( v10_waybel_0 @ C @ A )
                  & ( r3_waybel_9 @ A @ C @ B ) )
               => ( B
                  = ( k1_waybel_2 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( v8_pre_topc @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v1_compts_1 @ A )
          & ( l1_waybel_9 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v4_orders_2 @ C )
                  & ( v7_waybel_0 @ C )
                  & ( l1_waybel_0 @ C @ A ) )
               => ( ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) )
                    & ( v10_waybel_0 @ C @ A )
                    & ( r3_waybel_9 @ A @ C @ B ) )
                 => ( B
                    = ( k1_waybel_2 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_waybel_9])).

thf('1',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_waybel_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( k1_waybel_2 @ A @ B )
            = ( k4_yellow_2 @ A @ ( u1_waybel_0 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_waybel_0 @ X22 @ X23 )
      | ( ( k1_waybel_2 @ X23 @ X22 )
        = ( k4_yellow_2 @ X23 @ ( u1_waybel_0 @ X23 @ X22 ) ) )
      | ~ ( l1_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_waybel_2 @ sk_A @ sk_C_1 )
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k1_waybel_2 @ sk_A @ sk_C_1 )
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_waybel_2 @ sk_A @ sk_C_1 )
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(d5_yellow_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_yellow_2 @ A @ B )
            = ( k1_yellow_0 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k4_yellow_2 @ X25 @ X24 )
        = ( k1_yellow_0 @ X25 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( l1_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_2])).

thf('9',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('10',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('11',plain,(
    r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k4_yellow_2 @ X25 @ X24 )
        = ( k1_yellow_0 @ X25 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( l1_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_2])).

thf('15',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('16',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('17',plain,(
    r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l48_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v1_compts_1 @ A )
        & ( l1_waybel_9 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( C = D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) )
                      & ( v10_waybel_0 @ B @ A )
                      & ( r3_waybel_9 @ A @ B @ C ) )
                   => ( r2_lattice3 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) @ D ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( r2_lattice3 @ X28 @ ( k2_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_waybel_0 @ X28 @ X27 ) ) @ X29 )
      | ( X30 != X29 )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X30 )
      | ~ ( v10_waybel_0 @ X27 @ X28 )
      | ( m1_subset_1 @ ( sk_E @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_waybel_9 @ X28 )
      | ~ ( v1_compts_1 @ X28 )
      | ~ ( v2_lattice3 @ X28 )
      | ~ ( v1_lattice3 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[l48_waybel_9])).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v1_lattice3 @ X28 )
      | ~ ( v2_lattice3 @ X28 )
      | ~ ( v1_compts_1 @ X28 )
      | ~ ( l1_waybel_9 @ X28 )
      | ( m1_subset_1 @ ( sk_E @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v10_waybel_0 @ X27 @ X28 )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X29 )
      | ( r2_lattice3 @ X28 @ ( k2_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_waybel_0 @ X28 @ X27 ) ) @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_B )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_B )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26','27','28','29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v10_waybel_0 @ sk_C_1 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ~ ( v7_waybel_0 @ sk_C_1 )
    | ~ ( v4_orders_2 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','31'])).

thf('33',plain,(
    v10_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_waybel_0 @ X21 @ X20 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('36',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('39',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k2_relset_1 @ X4 @ X5 @ X3 )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v7_waybel_0 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_orders_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33','44','45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('53',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r1_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_lattice3 @ A @ B @ D )
                   => ( r1_orders_2 @ A @ C @ D ) ) )
              & ( r2_lattice3 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X15 @ X16 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_lattice3 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X17 ) )
      | ( r1_yellow_0 @ X17 @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','61'])).

thf('63',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('64',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_lattice3 @ X17 @ X16 @ ( sk_D_1 @ X15 @ X16 @ X17 ) )
      | ~ ( r2_lattice3 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X17 ) )
      | ( r1_yellow_0 @ X17 @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('75',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k4_yellow_2 @ X25 @ X24 )
        = ( k1_yellow_0 @ X25 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( l1_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_2])).

thf('76',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('77',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('78',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('79',plain,(
    r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','61'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('82',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(l49_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v1_compts_1 @ A )
        & ( l1_waybel_9 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( C = D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) )
                      & ( r3_waybel_9 @ A @ B @ C ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ( ( r2_lattice3 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) @ E )
                         => ( r3_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r2_lattice3 @ X32 @ ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) @ ( u1_waybel_0 @ X32 @ X31 ) ) @ X34 )
      | ( r3_orders_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ( X35 != X33 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X35 )
      | ( m1_subset_1 @ ( sk_E_1 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_waybel_9 @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( v2_lattice3 @ X32 )
      | ~ ( v1_lattice3 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[l49_waybel_9])).

thf('84',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_pre_topc @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v1_lattice3 @ X32 )
      | ~ ( v2_lattice3 @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( l1_waybel_9 @ X32 )
      | ( m1_subset_1 @ ( sk_E_1 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ( r3_orders_2 @ X32 @ X33 @ X34 )
      | ~ ( r2_lattice3 @ X32 @ ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) @ ( u1_waybel_0 @ X32 @ X31 ) ) @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v4_orders_2 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    v4_orders_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v7_waybel_0 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91','92','93','94','95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['81','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['80','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','61'])).

thf('106',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('108',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r3_orders_2 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','114'])).

thf('116',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['104','115'])).

thf('117',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_orders_2 @ X17 @ X15 @ ( sk_D_1 @ X15 @ X16 @ X17 ) )
      | ~ ( r2_lattice3 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X17 ) )
      | ( r1_yellow_0 @ X17 @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','123'])).

thf('125',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','125'])).

thf('127',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('130',plain,(
    r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('132',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('133',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('134',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ B )
           => ( ( C
                = ( k1_yellow_0 @ A @ B ) )
            <=> ( ( r2_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('135',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_lattice3 @ X11 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_D @ X13 @ X12 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ( X13
        = ( k1_yellow_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_yellow_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','139'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','140'])).

thf('142',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('144',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('145',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_lattice3 @ X11 @ X12 @ X13 )
      | ( r2_lattice3 @ X11 @ X12 @ ( sk_D @ X13 @ X12 @ X11 ) )
      | ( X13
        = ( k1_yellow_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_yellow_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','151'])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','152'])).

thf('154',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91','92','93','94','95','96','97'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['130','159'])).

thf('161',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['141'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['162','166'])).

thf('168',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_lattice3 @ X11 @ X12 @ X13 )
      | ~ ( r1_orders_2 @ X11 @ X13 @ ( sk_D @ X13 @ X12 @ X11 ) )
      | ( X13
        = ( k1_yellow_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_yellow_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('170',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['129','173'])).

thf('175',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','175'])).

thf('177',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','177'])).

thf('179',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','180'])).

thf('182',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('184',plain,(
    v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['181','184'])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['74','186'])).

thf('188',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X36: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X36 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('193',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r2_lattice3 @ X32 @ ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) @ ( u1_waybel_0 @ X32 @ X31 ) ) @ X34 )
      | ( r3_orders_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ( X35 != X33 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X35 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X32 @ ( sk_E_1 @ X32 ) ) @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_waybel_9 @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( v2_lattice3 @ X32 )
      | ~ ( v1_lattice3 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[l49_waybel_9])).

thf('194',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_pre_topc @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v1_lattice3 @ X32 )
      | ~ ( v2_lattice3 @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( l1_waybel_9 @ X32 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X32 @ ( sk_E_1 @ X32 ) ) @ X32 @ X32 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ( r3_orders_2 @ X32 @ X33 @ X34 )
      | ~ ( r2_lattice3 @ X32 @ ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) @ ( u1_waybel_0 @ X32 @ X31 ) ) @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v4_orders_2 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X1 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','194'])).

thf('196',plain,(
    v4_orders_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v7_waybel_0 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X1 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['195','196','197','198','199','200','201','202','203','204','205','206','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['191','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','214'])).

thf('216',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','114'])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_orders_2 @ X17 @ X15 @ ( sk_D_1 @ X15 @ X16 @ X17 ) )
      | ~ ( r2_lattice3 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X17 ) )
      | ( r1_yellow_0 @ X17 @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('222',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','226'])).

thf('228',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','228'])).

thf('230',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('233',plain,(
    r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('235',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','139'])).

thf('236',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('239',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','151'])).

thf('240',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['237','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['233','246'])).

thf('248',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('252',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['249','253'])).

thf('255',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_lattice3 @ X11 @ X12 @ X13 )
      | ~ ( r1_orders_2 @ X11 @ X13 @ ( sk_D @ X13 @ X12 @ X11 ) )
      | ( X13
        = ( k1_yellow_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_yellow_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('257',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('260',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['232','260'])).

thf('262',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['231','262'])).

thf('264',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','264'])).

thf('266',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['14','267'])).

thf('269',plain,(
    v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('270',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['270'])).

thf('272',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','271'])).

thf('273',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,(
    ! [X36: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X36 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( r2_lattice3 @ X28 @ ( k2_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_waybel_0 @ X28 @ X27 ) ) @ X29 )
      | ( X30 != X29 )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X30 )
      | ~ ( v10_waybel_0 @ X27 @ X28 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X28 @ ( sk_E @ X28 ) ) @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_waybel_9 @ X28 )
      | ~ ( v1_compts_1 @ X28 )
      | ~ ( v2_lattice3 @ X28 )
      | ~ ( v1_lattice3 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[l48_waybel_9])).

thf('278',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v1_lattice3 @ X28 )
      | ~ ( v2_lattice3 @ X28 )
      | ~ ( v1_compts_1 @ X28 )
      | ~ ( l1_waybel_9 @ X28 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X28 @ ( sk_E @ X28 ) ) @ X28 @ X28 )
      | ~ ( v10_waybel_0 @ X27 @ X28 )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X29 )
      | ( r2_lattice3 @ X28 @ ( k2_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_waybel_0 @ X28 @ X27 ) ) @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['277'])).

thf('279',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['276','278'])).

thf('280',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v10_waybel_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['279','280','281','282','283','284','285','286','287','288'])).

thf('290',plain,(
    ! [X0: $i] :
      ( ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','289'])).

thf('291',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( v4_orders_2 @ sk_C_1 )
    | ~ ( v7_waybel_0 @ sk_C_1 )
    | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ~ ( v10_waybel_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','290'])).

thf('292',plain,(
    v4_orders_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v7_waybel_0 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('296',plain,(
    v10_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['291','292','293','294','295','296'])).

thf('298',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('299',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('301',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('302',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('303',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('304',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('305',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('307',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k4_yellow_2 @ X25 @ X24 )
        = ( k1_yellow_0 @ X25 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( l1_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_2])).

thf('308',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('309',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('310',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('311',plain,(
    r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('313',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('314',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91','92','93','94','95','96','97'])).

thf('315',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['312','316'])).

thf('318',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['311','318'])).

thf('320',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['319','320'])).

thf('322',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('323',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('324',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['322','323'])).

thf('325',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['324'])).

thf('326',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['321','325'])).

thf('327',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['326'])).

thf('328',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_orders_2 @ X17 @ X15 @ ( sk_D_1 @ X15 @ X16 @ X17 ) )
      | ~ ( r2_lattice3 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X17 ) )
      | ( r1_yellow_0 @ X17 @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('329',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['327','328'])).

thf('330',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['329','330','331'])).

thf('333',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['310','333'])).

thf('335',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['309','335'])).

thf('337',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['336','337'])).

thf('339',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('340',plain,(
    r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['336','337'])).

thf('342',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('343',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('344',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('345',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['341','344'])).

thf('346',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['345'])).

thf('347',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['336','337'])).

thf('348',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('349',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('350',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['348','349'])).

thf('351',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['347','350'])).

thf('352',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['351'])).

thf('353',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91','92','93','94','95','96','97'])).

thf('354',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['352','353'])).

thf('355',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['354'])).

thf('356',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['346','355'])).

thf('357',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['356'])).

thf('358',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['340','357'])).

thf('359',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['358','359'])).

thf('361',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['345'])).

thf('362',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('363',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['361','362'])).

thf('364',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['363'])).

thf('365',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['360','364'])).

thf('366',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['365'])).

thf('367',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_lattice3 @ X11 @ X12 @ X13 )
      | ~ ( r1_orders_2 @ X11 @ X13 @ ( sk_D @ X13 @ X12 @ X11 ) )
      | ( X13
        = ( k1_yellow_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_yellow_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('368',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['366','367'])).

thf('369',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['368','369'])).

thf('371',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['339','371'])).

thf('373',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['372'])).

thf('374',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['338','373'])).

thf('375',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['374'])).

thf('376',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['308','375'])).

thf('377',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('378',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['376','377'])).

thf('379',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['307','378'])).

thf('380',plain,(
    v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('381',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['379','380'])).

thf('382',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['381'])).

thf('383',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['306','382'])).

thf('384',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['383','384'])).

thf('386',plain,(
    ! [X36: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X36 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['385','386'])).

thf('388',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X1 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['195','196','197','198','199','200','201','202','203','204','205','206','207'])).

thf('389',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['387','388'])).

thf('390',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['389'])).

thf('391',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['305','390'])).

thf('392',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['391'])).

thf('393',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['302','392'])).

thf('394',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['393'])).

thf('395',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['299','394'])).

thf('396',plain,(
    r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['395','396'])).

thf('398',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['324'])).

thf('399',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['397','398'])).

thf('400',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['399'])).

thf('401',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_orders_2 @ X17 @ X15 @ ( sk_D_1 @ X15 @ X16 @ X17 ) )
      | ~ ( r2_lattice3 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X17 ) )
      | ( r1_yellow_0 @ X17 @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('402',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['400','401'])).

thf('403',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('404',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('405',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['402','403','404'])).

thf('406',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['405'])).

thf('407',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['298','406'])).

thf('408',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['407'])).

thf('409',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','408'])).

thf('410',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('411',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['409','410'])).

thf('412',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('413',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('414',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['409','410'])).

thf('415',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('416',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['414','415'])).

thf('417',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['416'])).

thf('418',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['409','410'])).

thf('419',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['348','349'])).

thf('420',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['418','419'])).

thf('421',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['420'])).

thf('422',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['389'])).

thf('423',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['421','422'])).

thf('424',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['423'])).

thf('425',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['417','424'])).

thf('426',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['425'])).

thf('427',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['413','426'])).

thf('428',plain,(
    r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('429',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['427','428'])).

thf('430',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['416'])).

thf('431',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('432',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['430','431'])).

thf('433',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['432'])).

thf('434',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['429','433'])).

thf('435',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['434'])).

thf('436',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_lattice3 @ X11 @ X12 @ X13 )
      | ~ ( r1_orders_2 @ X11 @ X13 @ ( sk_D @ X13 @ X12 @ X11 ) )
      | ( X13
        = ( k1_yellow_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_yellow_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('437',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['435','436'])).

thf('438',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('439',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['437','438'])).

thf('440',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['439'])).

thf('441',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['412','440'])).

thf('442',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['441'])).

thf('443',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['411','442'])).

thf('444',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['443'])).

thf('445',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','444'])).

thf('446',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('447',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['445','446'])).

thf('448',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['8','447'])).

thf('449',plain,(
    v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('450',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['448','449'])).

thf('451',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['450'])).

thf('452',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','451'])).

thf('453',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('454',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['452','453'])).

thf('455',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('456',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['454','455'])).

thf('457',plain,
    ( ( sk_B
      = ( k1_waybel_2 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','456'])).

thf('458',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k1_waybel_2 @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['457'])).

thf('459',plain,(
    sk_B
 != ( k1_waybel_2 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('460',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['458','459'])).

thf('461',plain,(
    ! [X26: $i] :
      ( ( l1_orders_2 @ X26 )
      | ~ ( l1_waybel_9 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('462',plain,(
    ! [X10: $i] :
      ( ~ ( v1_lattice3 @ X10 )
      | ~ ( v2_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('463',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['461','462'])).

thf('464',plain,
    ( ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['460','463'])).

thf('465',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('466',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('467',plain,(
    $false ),
    inference(demod,[status(thm)],['464','465','466'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.52eycSYShv
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 11:09:05 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 2.04/2.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.04/2.25  % Solved by: fo/fo7.sh
% 2.04/2.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.04/2.25  % done 3597 iterations in 1.773s
% 2.04/2.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.04/2.25  % SZS output start Refutation
% 2.04/2.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.04/2.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.04/2.25  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 2.04/2.25  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 2.04/2.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.04/2.25  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.04/2.25  thf(sk_B_type, type, sk_B: $i).
% 2.04/2.25  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 2.04/2.25  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 2.04/2.25  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 2.04/2.25  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 2.04/2.25  thf(k1_waybel_2_type, type, k1_waybel_2: $i > $i > $i).
% 2.04/2.25  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 2.04/2.25  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 2.04/2.25  thf(sk_A_type, type, sk_A: $i).
% 2.04/2.25  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 2.04/2.25  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 2.04/2.25  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 2.04/2.25  thf(k4_yellow_2_type, type, k4_yellow_2: $i > $i > $i).
% 2.04/2.25  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 2.04/2.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.04/2.25  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 2.04/2.25  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 2.04/2.25  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 2.04/2.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.04/2.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.04/2.25  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 2.04/2.25  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 2.04/2.25  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.04/2.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.04/2.25  thf(v10_waybel_0_type, type, v10_waybel_0: $i > $i > $o).
% 2.04/2.25  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 2.04/2.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.04/2.25  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 2.04/2.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.04/2.25  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 2.04/2.25  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.04/2.25  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 2.04/2.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.04/2.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.04/2.25  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.04/2.25  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.04/2.25  thf(sk_E_type, type, sk_E: $i > $i).
% 2.04/2.25  thf(dt_l1_waybel_9, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 2.04/2.25  thf('0', plain, (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf(t35_waybel_9, conjecture,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 2.04/2.25         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 2.04/2.25         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 2.04/2.25       ( ![B:$i]:
% 2.04/2.25         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25           ( ![C:$i]:
% 2.04/2.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 2.04/2.25                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 2.04/2.25               ( ( ( ![D:$i]:
% 2.04/2.25                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25                       ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 2.04/2.25                   ( v10_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 2.04/2.25                 ( ( B ) = ( k1_waybel_2 @ A @ C ) ) ) ) ) ) ) ))).
% 2.04/2.25  thf(zf_stmt_0, negated_conjecture,
% 2.04/2.25    (~( ![A:$i]:
% 2.04/2.25        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 2.04/2.25            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 2.04/2.25            ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 2.04/2.25          ( ![B:$i]:
% 2.04/2.25            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25              ( ![C:$i]:
% 2.04/2.25                ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 2.04/2.25                    ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 2.04/2.25                  ( ( ( ![D:$i]:
% 2.04/2.25                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25                          ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 2.04/2.25                      ( v10_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 2.04/2.25                    ( ( B ) = ( k1_waybel_2 @ A @ C ) ) ) ) ) ) ) ) )),
% 2.04/2.25    inference('cnf.neg', [status(esa)], [t35_waybel_9])).
% 2.04/2.25  thf('1', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(d1_waybel_2, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 2.04/2.25       ( ![B:$i]:
% 2.04/2.25         ( ( l1_waybel_0 @ B @ A ) =>
% 2.04/2.25           ( ( k1_waybel_2 @ A @ B ) =
% 2.04/2.25             ( k4_yellow_2 @ A @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 2.04/2.25  thf('2', plain,
% 2.04/2.25      (![X22 : $i, X23 : $i]:
% 2.04/2.25         (~ (l1_waybel_0 @ X22 @ X23)
% 2.04/2.25          | ((k1_waybel_2 @ X23 @ X22)
% 2.04/2.25              = (k4_yellow_2 @ X23 @ (u1_waybel_0 @ X23 @ X22)))
% 2.04/2.25          | ~ (l1_orders_2 @ X23)
% 2.04/2.25          | (v2_struct_0 @ X23))),
% 2.04/2.25      inference('cnf', [status(esa)], [d1_waybel_2])).
% 2.04/2.25  thf('3', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ((k1_waybel_2 @ sk_A @ sk_C_1)
% 2.04/2.25            = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['1', '2'])).
% 2.04/2.25  thf('4', plain,
% 2.04/2.25      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.25        | ((k1_waybel_2 @ sk_A @ sk_C_1)
% 2.04/2.25            = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['0', '3'])).
% 2.04/2.25  thf('5', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('6', plain,
% 2.04/2.25      ((((k1_waybel_2 @ sk_A @ sk_C_1)
% 2.04/2.25          = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['4', '5'])).
% 2.04/2.25  thf('7', plain, (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf(d5_yellow_2, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 2.04/2.25       ( ![B:$i]:
% 2.04/2.25         ( ( v1_relat_1 @ B ) =>
% 2.04/2.25           ( ( k4_yellow_2 @ A @ B ) = ( k1_yellow_0 @ A @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 2.04/2.25  thf('8', plain,
% 2.04/2.25      (![X24 : $i, X25 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X24)
% 2.04/2.25          | ((k4_yellow_2 @ X25 @ X24)
% 2.04/2.25              = (k1_yellow_0 @ X25 @ (k2_relat_1 @ X24)))
% 2.04/2.25          | ~ (l1_orders_2 @ X25)
% 2.04/2.25          | (v2_struct_0 @ X25))),
% 2.04/2.25      inference('cnf', [status(esa)], [d5_yellow_2])).
% 2.04/2.25  thf('9', plain, (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('10', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('11', plain, ((r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('13', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('14', plain,
% 2.04/2.25      (![X24 : $i, X25 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X24)
% 2.04/2.25          | ((k4_yellow_2 @ X25 @ X24)
% 2.04/2.25              = (k1_yellow_0 @ X25 @ (k2_relat_1 @ X24)))
% 2.04/2.25          | ~ (l1_orders_2 @ X25)
% 2.04/2.25          | (v2_struct_0 @ X25))),
% 2.04/2.25      inference('cnf', [status(esa)], [d5_yellow_2])).
% 2.04/2.25  thf('15', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('16', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('17', plain, ((r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(l48_waybel_9, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 2.04/2.25         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 2.04/2.25         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 2.04/2.25       ( ![B:$i]:
% 2.04/2.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 2.04/2.25             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.04/2.25           ( ![C:$i]:
% 2.04/2.25             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25               ( ![D:$i]:
% 2.04/2.25                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25                   ( ( ( ( C ) = ( D ) ) & 
% 2.04/2.25                       ( ![E:$i]:
% 2.04/2.25                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 2.04/2.25                       ( v10_waybel_0 @ B @ A ) & ( r3_waybel_9 @ A @ B @ C ) ) =>
% 2.04/2.25                     ( r2_lattice3 @
% 2.04/2.25                       A @ 
% 2.04/2.25                       ( k2_relset_1 @
% 2.04/2.25                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.04/2.25                         ( u1_waybel_0 @ A @ B ) ) @ 
% 2.04/2.25                       D ) ) ) ) ) ) ) ) ))).
% 2.04/2.25  thf('19', plain,
% 2.04/2.25      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.04/2.25         ((v2_struct_0 @ X27)
% 2.04/2.25          | ~ (v4_orders_2 @ X27)
% 2.04/2.25          | ~ (v7_waybel_0 @ X27)
% 2.04/2.25          | ~ (l1_waybel_0 @ X27 @ X28)
% 2.04/2.25          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 2.04/2.25          | (r2_lattice3 @ X28 @ 
% 2.04/2.25             (k2_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28) @ 
% 2.04/2.25              (u1_waybel_0 @ X28 @ X27)) @ 
% 2.04/2.25             X29)
% 2.04/2.25          | ((X30) != (X29))
% 2.04/2.25          | ~ (r3_waybel_9 @ X28 @ X27 @ X30)
% 2.04/2.25          | ~ (v10_waybel_0 @ X27 @ X28)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ X28) @ (u1_struct_0 @ X28))
% 2.04/2.25          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 2.04/2.25          | ~ (l1_waybel_9 @ X28)
% 2.04/2.25          | ~ (v1_compts_1 @ X28)
% 2.04/2.25          | ~ (v2_lattice3 @ X28)
% 2.04/2.25          | ~ (v1_lattice3 @ X28)
% 2.04/2.25          | ~ (v5_orders_2 @ X28)
% 2.04/2.25          | ~ (v4_orders_2 @ X28)
% 2.04/2.25          | ~ (v3_orders_2 @ X28)
% 2.04/2.25          | ~ (v8_pre_topc @ X28)
% 2.04/2.25          | ~ (v2_pre_topc @ X28))),
% 2.04/2.25      inference('cnf', [status(esa)], [l48_waybel_9])).
% 2.04/2.25  thf('20', plain,
% 2.04/2.25      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.04/2.25         (~ (v2_pre_topc @ X28)
% 2.04/2.25          | ~ (v8_pre_topc @ X28)
% 2.04/2.25          | ~ (v3_orders_2 @ X28)
% 2.04/2.25          | ~ (v4_orders_2 @ X28)
% 2.04/2.25          | ~ (v5_orders_2 @ X28)
% 2.04/2.25          | ~ (v1_lattice3 @ X28)
% 2.04/2.25          | ~ (v2_lattice3 @ X28)
% 2.04/2.25          | ~ (v1_compts_1 @ X28)
% 2.04/2.25          | ~ (l1_waybel_9 @ X28)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ X28) @ (u1_struct_0 @ X28))
% 2.04/2.25          | ~ (v10_waybel_0 @ X27 @ X28)
% 2.04/2.25          | ~ (r3_waybel_9 @ X28 @ X27 @ X29)
% 2.04/2.25          | (r2_lattice3 @ X28 @ 
% 2.04/2.25             (k2_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28) @ 
% 2.04/2.25              (u1_waybel_0 @ X28 @ X27)) @ 
% 2.04/2.25             X29)
% 2.04/2.25          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 2.04/2.25          | ~ (l1_waybel_0 @ X27 @ X28)
% 2.04/2.25          | ~ (v7_waybel_0 @ X27)
% 2.04/2.25          | ~ (v4_orders_2 @ X27)
% 2.04/2.25          | (v2_struct_0 @ X27))),
% 2.04/2.25      inference('simplify', [status(thm)], ['19'])).
% 2.04/2.25  thf('21', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((v2_struct_0 @ X0)
% 2.04/2.25          | ~ (v4_orders_2 @ X0)
% 2.04/2.25          | ~ (v7_waybel_0 @ X0)
% 2.04/2.25          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 2.04/2.25          | (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25              (u1_waybel_0 @ sk_A @ X0)) @ 
% 2.04/2.25             sk_B)
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (l1_waybel_9 @ sk_A)
% 2.04/2.25          | ~ (v1_compts_1 @ sk_A)
% 2.04/2.25          | ~ (v2_lattice3 @ sk_A)
% 2.04/2.25          | ~ (v1_lattice3 @ sk_A)
% 2.04/2.25          | ~ (v5_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v4_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v3_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v8_pre_topc @ sk_A)
% 2.04/2.25          | ~ (v2_pre_topc @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['18', '20'])).
% 2.04/2.25  thf('22', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('23', plain, ((v1_compts_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('24', plain, ((v2_lattice3 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('25', plain, ((v1_lattice3 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('26', plain, ((v5_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('27', plain, ((v4_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('28', plain, ((v3_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('29', plain, ((v8_pre_topc @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('31', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((v2_struct_0 @ X0)
% 2.04/2.25          | ~ (v4_orders_2 @ X0)
% 2.04/2.25          | ~ (v7_waybel_0 @ X0)
% 2.04/2.25          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 2.04/2.25          | (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25              (u1_waybel_0 @ sk_A @ X0)) @ 
% 2.04/2.25             sk_B)
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)],
% 2.04/2.25                ['21', '22', '23', '24', '25', '26', '27', '28', '29', '30'])).
% 2.04/2.25  thf('32', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (v10_waybel_0 @ sk_C_1 @ sk_A)
% 2.04/2.25        | (r2_lattice3 @ sk_A @ 
% 2.04/2.25           (k2_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25            (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           sk_B)
% 2.04/2.25        | ~ (l1_waybel_0 @ sk_C_1 @ sk_A)
% 2.04/2.25        | ~ (v7_waybel_0 @ sk_C_1)
% 2.04/2.25        | ~ (v4_orders_2 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['17', '31'])).
% 2.04/2.25  thf('33', plain, ((v10_waybel_0 @ sk_C_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('34', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(dt_u1_waybel_0, axiom,
% 2.04/2.25    (![A:$i,B:$i]:
% 2.04/2.25     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.04/2.25       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 2.04/2.25         ( v1_funct_2 @
% 2.04/2.25           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.04/2.25         ( m1_subset_1 @
% 2.04/2.25           ( u1_waybel_0 @ A @ B ) @ 
% 2.04/2.25           ( k1_zfmisc_1 @
% 2.04/2.25             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.04/2.25  thf('35', plain,
% 2.04/2.25      (![X20 : $i, X21 : $i]:
% 2.04/2.25         (~ (l1_struct_0 @ X20)
% 2.04/2.25          | ~ (l1_waybel_0 @ X21 @ X20)
% 2.04/2.25          | (m1_subset_1 @ (u1_waybel_0 @ X20 @ X21) @ 
% 2.04/2.25             (k1_zfmisc_1 @ 
% 2.04/2.25              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20)))))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 2.04/2.25  thf('36', plain,
% 2.04/2.25      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C_1) @ 
% 2.04/2.25         (k1_zfmisc_1 @ 
% 2.04/2.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))))
% 2.04/2.25        | ~ (l1_struct_0 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['34', '35'])).
% 2.04/2.25  thf('37', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('38', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf(dt_l1_orders_2, axiom,
% 2.04/2.25    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 2.04/2.25  thf('39', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 2.04/2.25  thf('40', plain, (![X0 : $i]: (~ (l1_waybel_9 @ X0) | (l1_struct_0 @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['38', '39'])).
% 2.04/2.25  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 2.04/2.25      inference('sup-', [status(thm)], ['37', '40'])).
% 2.04/2.25  thf('42', plain,
% 2.04/2.25      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C_1) @ 
% 2.04/2.25        (k1_zfmisc_1 @ 
% 2.04/2.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))))),
% 2.04/2.25      inference('demod', [status(thm)], ['36', '41'])).
% 2.04/2.25  thf(redefinition_k2_relset_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.04/2.25       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.04/2.25  thf('43', plain,
% 2.04/2.25      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.04/2.25         (((k2_relset_1 @ X4 @ X5 @ X3) = (k2_relat_1 @ X3))
% 2.04/2.25          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.04/2.25      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.04/2.25  thf('44', plain,
% 2.04/2.25      (((k2_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25         (u1_waybel_0 @ sk_A @ sk_C_1))
% 2.04/2.25         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['42', '43'])).
% 2.04/2.25  thf('45', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('46', plain, ((v7_waybel_0 @ sk_C_1)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('47', plain, ((v4_orders_2 @ sk_C_1)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('48', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           sk_B)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('demod', [status(thm)], ['32', '33', '44', '45', '46', '47'])).
% 2.04/2.25  thf('49', plain, (~ (v2_struct_0 @ sk_C_1)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('50', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('clc', [status(thm)], ['48', '49'])).
% 2.04/2.25  thf('51', plain, ((r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('52', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('clc', [status(thm)], ['48', '49'])).
% 2.04/2.25  thf('53', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('54', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(t15_yellow_0, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.04/2.25       ( ![B:$i]:
% 2.04/2.25         ( ( r1_yellow_0 @ A @ B ) <=>
% 2.04/2.25           ( ?[C:$i]:
% 2.04/2.25             ( ( ![D:$i]:
% 2.04/2.25                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25                   ( ( r2_lattice3 @ A @ B @ D ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) & 
% 2.04/2.25               ( r2_lattice3 @ A @ B @ C ) & 
% 2.04/2.25               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 2.04/2.25  thf('55', plain,
% 2.04/2.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.04/2.25         ((m1_subset_1 @ (sk_D_1 @ X15 @ X16 @ X17) @ (u1_struct_0 @ X17))
% 2.04/2.25          | ~ (r2_lattice3 @ X17 @ X16 @ X15)
% 2.04/2.25          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X17))
% 2.04/2.25          | (r1_yellow_0 @ X17 @ X16)
% 2.04/2.25          | ~ (l1_orders_2 @ X17)
% 2.04/2.25          | ~ (v5_orders_2 @ X17))),
% 2.04/2.25      inference('cnf', [status(esa)], [t15_yellow_0])).
% 2.04/2.25  thf('56', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (v5_orders_2 @ sk_A)
% 2.04/2.25          | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ X0)
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (m1_subset_1 @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['54', '55'])).
% 2.04/2.25  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('58', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (l1_orders_2 @ sk_A)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ X0)
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (m1_subset_1 @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)], ['56', '57'])).
% 2.04/2.25  thf('59', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (l1_waybel_9 @ sk_A)
% 2.04/2.25          | (m1_subset_1 @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['53', '58'])).
% 2.04/2.25  thf('60', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('61', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((m1_subset_1 @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['59', '60'])).
% 2.04/2.25  thf('62', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['52', '61'])).
% 2.04/2.25  thf('63', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('clc', [status(thm)], ['48', '49'])).
% 2.04/2.25  thf('64', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('65', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('66', plain,
% 2.04/2.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.04/2.25         ((r2_lattice3 @ X17 @ X16 @ (sk_D_1 @ X15 @ X16 @ X17))
% 2.04/2.25          | ~ (r2_lattice3 @ X17 @ X16 @ X15)
% 2.04/2.25          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X17))
% 2.04/2.25          | (r1_yellow_0 @ X17 @ X16)
% 2.04/2.25          | ~ (l1_orders_2 @ X17)
% 2.04/2.25          | ~ (v5_orders_2 @ X17))),
% 2.04/2.25      inference('cnf', [status(esa)], [t15_yellow_0])).
% 2.04/2.25  thf('67', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (v5_orders_2 @ sk_A)
% 2.04/2.25          | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ X0)
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r2_lattice3 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ X0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['65', '66'])).
% 2.04/2.25  thf('68', plain, ((v5_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('69', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (l1_orders_2 @ sk_A)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ X0)
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r2_lattice3 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ X0 @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)], ['67', '68'])).
% 2.04/2.25  thf('70', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (l1_waybel_9 @ sk_A)
% 2.04/2.25          | (r2_lattice3 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ X0 @ sk_A))
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['64', '69'])).
% 2.04/2.25  thf('71', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('72', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((r2_lattice3 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ X0 @ sk_A))
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['70', '71'])).
% 2.04/2.25  thf('73', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['63', '72'])).
% 2.04/2.25  thf('74', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('75', plain,
% 2.04/2.25      (![X24 : $i, X25 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X24)
% 2.04/2.25          | ((k4_yellow_2 @ X25 @ X24)
% 2.04/2.25              = (k1_yellow_0 @ X25 @ (k2_relat_1 @ X24)))
% 2.04/2.25          | ~ (l1_orders_2 @ X25)
% 2.04/2.25          | (v2_struct_0 @ X25))),
% 2.04/2.25      inference('cnf', [status(esa)], [d5_yellow_2])).
% 2.04/2.25  thf('76', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('77', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('78', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('clc', [status(thm)], ['48', '49'])).
% 2.04/2.25  thf('79', plain, ((r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('80', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['52', '61'])).
% 2.04/2.25  thf('81', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['63', '72'])).
% 2.04/2.25  thf('82', plain,
% 2.04/2.25      (((k2_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25         (u1_waybel_0 @ sk_A @ sk_C_1))
% 2.04/2.25         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['42', '43'])).
% 2.04/2.25  thf(l49_waybel_9, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 2.04/2.25         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 2.04/2.25         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 2.04/2.25       ( ![B:$i]:
% 2.04/2.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 2.04/2.25             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.04/2.25           ( ![C:$i]:
% 2.04/2.25             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25               ( ![D:$i]:
% 2.04/2.25                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25                   ( ( ( ( C ) = ( D ) ) & 
% 2.04/2.25                       ( ![E:$i]:
% 2.04/2.25                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 2.04/2.25                       ( r3_waybel_9 @ A @ B @ C ) ) =>
% 2.04/2.25                     ( ![E:$i]:
% 2.04/2.25                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25                         ( ( r2_lattice3 @
% 2.04/2.25                             A @ 
% 2.04/2.25                             ( k2_relset_1 @
% 2.04/2.25                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.04/2.25                               ( u1_waybel_0 @ A @ B ) ) @ 
% 2.04/2.25                             E ) =>
% 2.04/2.25                           ( r3_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.04/2.25  thf('83', plain,
% 2.04/2.25      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.04/2.25         ((v2_struct_0 @ X31)
% 2.04/2.25          | ~ (v4_orders_2 @ X31)
% 2.04/2.25          | ~ (v7_waybel_0 @ X31)
% 2.04/2.25          | ~ (l1_waybel_0 @ X31 @ X32)
% 2.04/2.25          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 2.04/2.25          | ~ (r2_lattice3 @ X32 @ 
% 2.04/2.25               (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 2.04/2.25                (u1_waybel_0 @ X32 @ X31)) @ 
% 2.04/2.25               X34)
% 2.04/2.25          | (r3_orders_2 @ X32 @ X33 @ X34)
% 2.04/2.25          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 2.04/2.25          | ((X35) != (X33))
% 2.04/2.25          | ~ (r3_waybel_9 @ X32 @ X31 @ X35)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ X32) @ (u1_struct_0 @ X32))
% 2.04/2.25          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X32))
% 2.04/2.25          | ~ (l1_waybel_9 @ X32)
% 2.04/2.25          | ~ (v1_compts_1 @ X32)
% 2.04/2.25          | ~ (v2_lattice3 @ X32)
% 2.04/2.25          | ~ (v1_lattice3 @ X32)
% 2.04/2.25          | ~ (v5_orders_2 @ X32)
% 2.04/2.25          | ~ (v4_orders_2 @ X32)
% 2.04/2.25          | ~ (v3_orders_2 @ X32)
% 2.04/2.25          | ~ (v8_pre_topc @ X32)
% 2.04/2.25          | ~ (v2_pre_topc @ X32))),
% 2.04/2.25      inference('cnf', [status(esa)], [l49_waybel_9])).
% 2.04/2.25  thf('84', plain,
% 2.04/2.25      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.04/2.25         (~ (v2_pre_topc @ X32)
% 2.04/2.25          | ~ (v8_pre_topc @ X32)
% 2.04/2.25          | ~ (v3_orders_2 @ X32)
% 2.04/2.25          | ~ (v4_orders_2 @ X32)
% 2.04/2.25          | ~ (v5_orders_2 @ X32)
% 2.04/2.25          | ~ (v1_lattice3 @ X32)
% 2.04/2.25          | ~ (v2_lattice3 @ X32)
% 2.04/2.25          | ~ (v1_compts_1 @ X32)
% 2.04/2.25          | ~ (l1_waybel_9 @ X32)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ X32) @ (u1_struct_0 @ X32))
% 2.04/2.25          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 2.04/2.25          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 2.04/2.25          | (r3_orders_2 @ X32 @ X33 @ X34)
% 2.04/2.25          | ~ (r2_lattice3 @ X32 @ 
% 2.04/2.25               (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 2.04/2.25                (u1_waybel_0 @ X32 @ X31)) @ 
% 2.04/2.25               X34)
% 2.04/2.25          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 2.04/2.25          | ~ (l1_waybel_0 @ X31 @ X32)
% 2.04/2.25          | ~ (v7_waybel_0 @ X31)
% 2.04/2.25          | ~ (v4_orders_2 @ X31)
% 2.04/2.25          | (v2_struct_0 @ X31))),
% 2.04/2.25      inference('simplify', [status(thm)], ['83'])).
% 2.04/2.25  thf('85', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (v4_orders_2 @ sk_C_1)
% 2.04/2.25          | ~ (v7_waybel_0 @ sk_C_1)
% 2.04/2.25          | ~ (l1_waybel_0 @ sk_C_1 @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (l1_waybel_9 @ sk_A)
% 2.04/2.25          | ~ (v1_compts_1 @ sk_A)
% 2.04/2.25          | ~ (v2_lattice3 @ sk_A)
% 2.04/2.25          | ~ (v1_lattice3 @ sk_A)
% 2.04/2.25          | ~ (v5_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v4_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v3_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v8_pre_topc @ sk_A)
% 2.04/2.25          | ~ (v2_pre_topc @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['82', '84'])).
% 2.04/2.25  thf('86', plain, ((v4_orders_2 @ sk_C_1)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('87', plain, ((v7_waybel_0 @ sk_C_1)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('88', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('89', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('90', plain, ((v1_compts_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('91', plain, ((v2_lattice3 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('92', plain, ((v1_lattice3 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('93', plain, ((v5_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('94', plain, ((v4_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('95', plain, ((v3_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('96', plain, ((v8_pre_topc @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('98', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)],
% 2.04/2.25                ['85', '86', '87', '88', '89', '90', '91', '92', '93', '94', 
% 2.04/2.25                 '95', '96', '97'])).
% 2.04/2.25  thf('99', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ 
% 2.04/2.25               (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25                sk_A) @ 
% 2.04/2.25               (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['81', '98'])).
% 2.04/2.25  thf('100', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['80', '99'])).
% 2.04/2.25  thf('101', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['100'])).
% 2.04/2.25  thf('102', plain,
% 2.04/2.25      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['79', '101'])).
% 2.04/2.25  thf('103', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('104', plain,
% 2.04/2.25      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)], ['102', '103'])).
% 2.04/2.25  thf('105', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['52', '61'])).
% 2.04/2.25  thf('106', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('107', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(redefinition_r3_orders_2, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.04/2.25         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 2.04/2.25         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 2.04/2.25       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 2.04/2.25  thf('108', plain,
% 2.04/2.25      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 2.04/2.25          | ~ (l1_orders_2 @ X8)
% 2.04/2.25          | ~ (v3_orders_2 @ X8)
% 2.04/2.25          | (v2_struct_0 @ X8)
% 2.04/2.25          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 2.04/2.25          | (r1_orders_2 @ X8 @ X7 @ X9)
% 2.04/2.25          | ~ (r3_orders_2 @ X8 @ X7 @ X9))),
% 2.04/2.25      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 2.04/2.25  thf('109', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.25          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ~ (v3_orders_2 @ sk_A)
% 2.04/2.25          | ~ (l1_orders_2 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['107', '108'])).
% 2.04/2.25  thf('110', plain, ((v3_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('111', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.25          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ~ (l1_orders_2 @ sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['109', '110'])).
% 2.04/2.25  thf('112', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (l1_waybel_9 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.25          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['106', '111'])).
% 2.04/2.25  thf('113', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('114', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((v2_struct_0 @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.25          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['112', '113'])).
% 2.04/2.25  thf('115', plain,
% 2.04/2.25      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['105', '114'])).
% 2.04/2.25  thf('116', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['104', '115'])).
% 2.04/2.25  thf('117', plain,
% 2.04/2.25      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25         (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['116'])).
% 2.04/2.25  thf('118', plain,
% 2.04/2.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.04/2.25         (~ (r1_orders_2 @ X17 @ X15 @ (sk_D_1 @ X15 @ X16 @ X17))
% 2.04/2.25          | ~ (r2_lattice3 @ X17 @ X16 @ X15)
% 2.04/2.25          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X17))
% 2.04/2.25          | (r1_yellow_0 @ X17 @ X16)
% 2.04/2.25          | ~ (l1_orders_2 @ X17)
% 2.04/2.25          | ~ (v5_orders_2 @ X17))),
% 2.04/2.25      inference('cnf', [status(esa)], [t15_yellow_0])).
% 2.04/2.25  thf('119', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (v5_orders_2 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.25      inference('sup-', [status(thm)], ['117', '118'])).
% 2.04/2.25  thf('120', plain, ((v5_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('121', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('122', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.25      inference('demod', [status(thm)], ['119', '120', '121'])).
% 2.04/2.25  thf('123', plain,
% 2.04/2.25      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           sk_B)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['122'])).
% 2.04/2.25  thf('124', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['78', '123'])).
% 2.04/2.25  thf('125', plain,
% 2.04/2.25      ((~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['124'])).
% 2.04/2.25  thf('126', plain,
% 2.04/2.25      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['77', '125'])).
% 2.04/2.25  thf('127', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('128', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['126', '127'])).
% 2.04/2.25  thf('129', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('clc', [status(thm)], ['48', '49'])).
% 2.04/2.25  thf('130', plain, ((r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('131', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['126', '127'])).
% 2.04/2.25  thf('132', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('clc', [status(thm)], ['48', '49'])).
% 2.04/2.25  thf('133', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('134', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(d9_yellow_0, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( l1_orders_2 @ A ) =>
% 2.04/2.25       ( ![B:$i,C:$i]:
% 2.04/2.25         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25           ( ( r1_yellow_0 @ A @ B ) =>
% 2.04/2.25             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 2.04/2.25               ( ( r2_lattice3 @ A @ B @ C ) & 
% 2.04/2.25                 ( ![D:$i]:
% 2.04/2.25                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.25                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 2.04/2.25                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 2.04/2.25  thf('135', plain,
% 2.04/2.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ X11 @ X12 @ X13)
% 2.04/2.25          | (m1_subset_1 @ (sk_D @ X13 @ X12 @ X11) @ (u1_struct_0 @ X11))
% 2.04/2.25          | ((X13) = (k1_yellow_0 @ X11 @ X12))
% 2.04/2.25          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 2.04/2.25          | ~ (r1_yellow_0 @ X11 @ X12)
% 2.04/2.25          | ~ (l1_orders_2 @ X11))),
% 2.04/2.25      inference('cnf', [status(esa)], [d9_yellow_0])).
% 2.04/2.25  thf('136', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (l1_orders_2 @ sk_A)
% 2.04/2.25          | ~ (r1_yellow_0 @ sk_A @ X0)
% 2.04/2.25          | ((sk_B) = (k1_yellow_0 @ sk_A @ X0))
% 2.04/2.25          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 2.04/2.25      inference('sup-', [status(thm)], ['134', '135'])).
% 2.04/2.25  thf('137', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (l1_waybel_9 @ sk_A)
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B) = (k1_yellow_0 @ sk_A @ X0))
% 2.04/2.25          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['133', '136'])).
% 2.04/2.25  thf('138', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('139', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B) = (k1_yellow_0 @ sk_A @ X0))
% 2.04/2.25          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['137', '138'])).
% 2.04/2.25  thf('140', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['132', '139'])).
% 2.04/2.25  thf('141', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['131', '140'])).
% 2.04/2.25  thf('142', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('simplify', [status(thm)], ['141'])).
% 2.04/2.25  thf('143', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['126', '127'])).
% 2.04/2.25  thf('144', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('clc', [status(thm)], ['48', '49'])).
% 2.04/2.25  thf('145', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('146', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('147', plain,
% 2.04/2.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ X11 @ X12 @ X13)
% 2.04/2.25          | (r2_lattice3 @ X11 @ X12 @ (sk_D @ X13 @ X12 @ X11))
% 2.04/2.25          | ((X13) = (k1_yellow_0 @ X11 @ X12))
% 2.04/2.25          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 2.04/2.25          | ~ (r1_yellow_0 @ X11 @ X12)
% 2.04/2.25          | ~ (l1_orders_2 @ X11))),
% 2.04/2.25      inference('cnf', [status(esa)], [d9_yellow_0])).
% 2.04/2.25  thf('148', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (l1_orders_2 @ sk_A)
% 2.04/2.25          | ~ (r1_yellow_0 @ sk_A @ X0)
% 2.04/2.25          | ((sk_B) = (k1_yellow_0 @ sk_A @ X0))
% 2.04/2.25          | (r2_lattice3 @ sk_A @ X0 @ (sk_D @ sk_B @ X0 @ sk_A))
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 2.04/2.25      inference('sup-', [status(thm)], ['146', '147'])).
% 2.04/2.25  thf('149', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (l1_waybel_9 @ sk_A)
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r2_lattice3 @ sk_A @ X0 @ (sk_D @ sk_B @ X0 @ sk_A))
% 2.04/2.25          | ((sk_B) = (k1_yellow_0 @ sk_A @ X0))
% 2.04/2.25          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['145', '148'])).
% 2.04/2.25  thf('150', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('151', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r2_lattice3 @ sk_A @ X0 @ (sk_D @ sk_B @ X0 @ sk_A))
% 2.04/2.25          | ((sk_B) = (k1_yellow_0 @ sk_A @ X0))
% 2.04/2.25          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['149', '150'])).
% 2.04/2.25  thf('152', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['144', '151'])).
% 2.04/2.25  thf('153', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['143', '152'])).
% 2.04/2.25  thf('154', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('simplify', [status(thm)], ['153'])).
% 2.04/2.25  thf('155', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)],
% 2.04/2.25                ['85', '86', '87', '88', '89', '90', '91', '92', '93', '94', 
% 2.04/2.25                 '95', '96', '97'])).
% 2.04/2.25  thf('156', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B)
% 2.04/2.25              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ 
% 2.04/2.25               (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25                sk_A) @ 
% 2.04/2.25               (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['154', '155'])).
% 2.04/2.25  thf('157', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ 
% 2.04/2.25               (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25                sk_A) @ 
% 2.04/2.25               (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | ((sk_B)
% 2.04/2.25              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('simplify', [status(thm)], ['156'])).
% 2.04/2.25  thf('158', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B)
% 2.04/2.25              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B)
% 2.04/2.25              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['142', '157'])).
% 2.04/2.25  thf('159', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | ((sk_B)
% 2.04/2.25              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('simplify', [status(thm)], ['158'])).
% 2.04/2.25  thf('160', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['130', '159'])).
% 2.04/2.25  thf('161', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('162', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)], ['160', '161'])).
% 2.04/2.25  thf('163', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('simplify', [status(thm)], ['141'])).
% 2.04/2.25  thf('164', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((v2_struct_0 @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.25          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['112', '113'])).
% 2.04/2.25  thf('165', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['163', '164'])).
% 2.04/2.25  thf('166', plain,
% 2.04/2.25      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25         (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('simplify', [status(thm)], ['165'])).
% 2.04/2.25  thf('167', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['162', '166'])).
% 2.04/2.25  thf('168', plain,
% 2.04/2.25      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25         (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['167'])).
% 2.04/2.25  thf('169', plain,
% 2.04/2.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ X11 @ X12 @ X13)
% 2.04/2.25          | ~ (r1_orders_2 @ X11 @ X13 @ (sk_D @ X13 @ X12 @ X11))
% 2.04/2.25          | ((X13) = (k1_yellow_0 @ X11 @ X12))
% 2.04/2.25          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 2.04/2.25          | ~ (r1_yellow_0 @ X11 @ X12)
% 2.04/2.25          | ~ (l1_orders_2 @ X11))),
% 2.04/2.25      inference('cnf', [status(esa)], [d9_yellow_0])).
% 2.04/2.25  thf('170', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.25      inference('sup-', [status(thm)], ['168', '169'])).
% 2.04/2.25  thf('171', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('172', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.25      inference('demod', [status(thm)], ['170', '171'])).
% 2.04/2.25  thf('173', plain,
% 2.04/2.25      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           sk_B)
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['172'])).
% 2.04/2.25  thf('174', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['129', '173'])).
% 2.04/2.25  thf('175', plain,
% 2.04/2.25      ((~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['174'])).
% 2.04/2.25  thf('176', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['128', '175'])).
% 2.04/2.25  thf('177', plain,
% 2.04/2.25      ((~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('simplify', [status(thm)], ['176'])).
% 2.04/2.25  thf('178', plain,
% 2.04/2.25      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['76', '177'])).
% 2.04/2.25  thf('179', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('180', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.25      inference('demod', [status(thm)], ['178', '179'])).
% 2.04/2.25  thf('181', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ~ (v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('sup+', [status(thm)], ['75', '180'])).
% 2.04/2.25  thf('182', plain,
% 2.04/2.25      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C_1) @ 
% 2.04/2.25        (k1_zfmisc_1 @ 
% 2.04/2.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))))),
% 2.04/2.25      inference('demod', [status(thm)], ['36', '41'])).
% 2.04/2.25  thf(cc1_relset_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.04/2.25       ( v1_relat_1 @ C ) ))).
% 2.04/2.25  thf('183', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.25         ((v1_relat_1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 2.04/2.25      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.04/2.25  thf('184', plain, ((v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['182', '183'])).
% 2.04/2.25  thf('185', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['181', '184'])).
% 2.04/2.25  thf('186', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['185'])).
% 2.04/2.25  thf('187', plain,
% 2.04/2.25      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['74', '186'])).
% 2.04/2.25  thf('188', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('189', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('demod', [status(thm)], ['187', '188'])).
% 2.04/2.25  thf('190', plain,
% 2.04/2.25      (![X36 : $i]:
% 2.04/2.25         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X36) @ sk_A @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('191', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['189', '190'])).
% 2.04/2.25  thf('192', plain,
% 2.04/2.25      (((k2_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25         (u1_waybel_0 @ sk_A @ sk_C_1))
% 2.04/2.25         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['42', '43'])).
% 2.04/2.25  thf('193', plain,
% 2.04/2.25      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.04/2.25         ((v2_struct_0 @ X31)
% 2.04/2.25          | ~ (v4_orders_2 @ X31)
% 2.04/2.25          | ~ (v7_waybel_0 @ X31)
% 2.04/2.25          | ~ (l1_waybel_0 @ X31 @ X32)
% 2.04/2.25          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 2.04/2.25          | ~ (r2_lattice3 @ X32 @ 
% 2.04/2.25               (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 2.04/2.25                (u1_waybel_0 @ X32 @ X31)) @ 
% 2.04/2.25               X34)
% 2.04/2.25          | (r3_orders_2 @ X32 @ X33 @ X34)
% 2.04/2.25          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 2.04/2.25          | ((X35) != (X33))
% 2.04/2.25          | ~ (r3_waybel_9 @ X32 @ X31 @ X35)
% 2.04/2.25          | ~ (v5_pre_topc @ (k4_waybel_1 @ X32 @ (sk_E_1 @ X32)) @ X32 @ X32)
% 2.04/2.25          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X32))
% 2.04/2.25          | ~ (l1_waybel_9 @ X32)
% 2.04/2.25          | ~ (v1_compts_1 @ X32)
% 2.04/2.25          | ~ (v2_lattice3 @ X32)
% 2.04/2.25          | ~ (v1_lattice3 @ X32)
% 2.04/2.25          | ~ (v5_orders_2 @ X32)
% 2.04/2.25          | ~ (v4_orders_2 @ X32)
% 2.04/2.25          | ~ (v3_orders_2 @ X32)
% 2.04/2.25          | ~ (v8_pre_topc @ X32)
% 2.04/2.25          | ~ (v2_pre_topc @ X32))),
% 2.04/2.25      inference('cnf', [status(esa)], [l49_waybel_9])).
% 2.04/2.25  thf('194', plain,
% 2.04/2.25      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.04/2.25         (~ (v2_pre_topc @ X32)
% 2.04/2.25          | ~ (v8_pre_topc @ X32)
% 2.04/2.25          | ~ (v3_orders_2 @ X32)
% 2.04/2.25          | ~ (v4_orders_2 @ X32)
% 2.04/2.25          | ~ (v5_orders_2 @ X32)
% 2.04/2.25          | ~ (v1_lattice3 @ X32)
% 2.04/2.25          | ~ (v2_lattice3 @ X32)
% 2.04/2.25          | ~ (v1_compts_1 @ X32)
% 2.04/2.25          | ~ (l1_waybel_9 @ X32)
% 2.04/2.25          | ~ (v5_pre_topc @ (k4_waybel_1 @ X32 @ (sk_E_1 @ X32)) @ X32 @ X32)
% 2.04/2.25          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 2.04/2.25          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 2.04/2.25          | (r3_orders_2 @ X32 @ X33 @ X34)
% 2.04/2.25          | ~ (r2_lattice3 @ X32 @ 
% 2.04/2.25               (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 2.04/2.25                (u1_waybel_0 @ X32 @ X31)) @ 
% 2.04/2.25               X34)
% 2.04/2.25          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 2.04/2.25          | ~ (l1_waybel_0 @ X31 @ X32)
% 2.04/2.25          | ~ (v7_waybel_0 @ X31)
% 2.04/2.25          | ~ (v4_orders_2 @ X31)
% 2.04/2.25          | (v2_struct_0 @ X31))),
% 2.04/2.25      inference('simplify', [status(thm)], ['193'])).
% 2.04/2.25  thf('195', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (v4_orders_2 @ sk_C_1)
% 2.04/2.25          | ~ (v7_waybel_0 @ sk_C_1)
% 2.04/2.25          | ~ (l1_waybel_0 @ sk_C_1 @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X1)
% 2.04/2.25          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 2.04/2.25               sk_A)
% 2.04/2.25          | ~ (l1_waybel_9 @ sk_A)
% 2.04/2.25          | ~ (v1_compts_1 @ sk_A)
% 2.04/2.25          | ~ (v2_lattice3 @ sk_A)
% 2.04/2.25          | ~ (v1_lattice3 @ sk_A)
% 2.04/2.25          | ~ (v5_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v4_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v3_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v8_pre_topc @ sk_A)
% 2.04/2.25          | ~ (v2_pre_topc @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['192', '194'])).
% 2.04/2.25  thf('196', plain, ((v4_orders_2 @ sk_C_1)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('197', plain, ((v7_waybel_0 @ sk_C_1)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('198', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('199', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('200', plain, ((v1_compts_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('201', plain, ((v2_lattice3 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('202', plain, ((v1_lattice3 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('203', plain, ((v5_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('204', plain, ((v4_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('205', plain, ((v3_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('206', plain, ((v8_pre_topc @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('207', plain, ((v2_pre_topc @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('208', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X1)
% 2.04/2.25          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 2.04/2.25               sk_A))),
% 2.04/2.25      inference('demod', [status(thm)],
% 2.04/2.25                ['195', '196', '197', '198', '199', '200', '201', '202', 
% 2.04/2.25                 '203', '204', '205', '206', '207'])).
% 2.04/2.25  thf('209', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ X1)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['191', '208'])).
% 2.04/2.25  thf('210', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X1)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ X1)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['209'])).
% 2.04/2.25  thf('211', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ 
% 2.04/2.25               (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25                sk_A) @ 
% 2.04/2.25               (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['73', '210'])).
% 2.04/2.25  thf('212', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ 
% 2.04/2.25               (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25                sk_A) @ 
% 2.04/2.25               (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['211'])).
% 2.04/2.25  thf('213', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['62', '212'])).
% 2.04/2.25  thf('214', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['213'])).
% 2.04/2.25  thf('215', plain,
% 2.04/2.25      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['51', '214'])).
% 2.04/2.25  thf('216', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('217', plain,
% 2.04/2.25      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)], ['215', '216'])).
% 2.04/2.25  thf('218', plain,
% 2.04/2.25      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['105', '114'])).
% 2.04/2.25  thf('219', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['217', '218'])).
% 2.04/2.25  thf('220', plain,
% 2.04/2.25      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25         (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('simplify', [status(thm)], ['219'])).
% 2.04/2.25  thf('221', plain,
% 2.04/2.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.04/2.25         (~ (r1_orders_2 @ X17 @ X15 @ (sk_D_1 @ X15 @ X16 @ X17))
% 2.04/2.25          | ~ (r2_lattice3 @ X17 @ X16 @ X15)
% 2.04/2.25          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X17))
% 2.04/2.25          | (r1_yellow_0 @ X17 @ X16)
% 2.04/2.25          | ~ (l1_orders_2 @ X17)
% 2.04/2.25          | ~ (v5_orders_2 @ X17))),
% 2.04/2.25      inference('cnf', [status(esa)], [t15_yellow_0])).
% 2.04/2.25  thf('222', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (v5_orders_2 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.25      inference('sup-', [status(thm)], ['220', '221'])).
% 2.04/2.25  thf('223', plain, ((v5_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('224', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('225', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.25      inference('demod', [status(thm)], ['222', '223', '224'])).
% 2.04/2.25  thf('226', plain,
% 2.04/2.25      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           sk_B)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('simplify', [status(thm)], ['225'])).
% 2.04/2.25  thf('227', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['50', '226'])).
% 2.04/2.25  thf('228', plain,
% 2.04/2.25      ((~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['227'])).
% 2.04/2.25  thf('229', plain,
% 2.04/2.25      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['16', '228'])).
% 2.04/2.25  thf('230', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('231', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('demod', [status(thm)], ['229', '230'])).
% 2.04/2.25  thf('232', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('clc', [status(thm)], ['48', '49'])).
% 2.04/2.25  thf('233', plain, ((r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('234', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('demod', [status(thm)], ['229', '230'])).
% 2.04/2.25  thf('235', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['132', '139'])).
% 2.04/2.25  thf('236', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['234', '235'])).
% 2.04/2.25  thf('237', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['236'])).
% 2.04/2.25  thf('238', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('demod', [status(thm)], ['229', '230'])).
% 2.04/2.25  thf('239', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['144', '151'])).
% 2.04/2.25  thf('240', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['238', '239'])).
% 2.04/2.25  thf('241', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['240'])).
% 2.04/2.25  thf('242', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X1)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ X1)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['209'])).
% 2.04/2.25  thf('243', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B)
% 2.04/2.25              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ 
% 2.04/2.25               (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25                sk_A) @ 
% 2.04/2.25               (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['241', '242'])).
% 2.04/2.25  thf('244', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ 
% 2.04/2.25               (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25                sk_A) @ 
% 2.04/2.25               (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | ((sk_B)
% 2.04/2.25              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['243'])).
% 2.04/2.25  thf('245', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B)
% 2.04/2.25              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B)
% 2.04/2.25              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['237', '244'])).
% 2.04/2.25  thf('246', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | ((sk_B)
% 2.04/2.25              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['245'])).
% 2.04/2.25  thf('247', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['233', '246'])).
% 2.04/2.25  thf('248', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('249', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)], ['247', '248'])).
% 2.04/2.25  thf('250', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['236'])).
% 2.04/2.25  thf('251', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((v2_struct_0 @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.25          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['112', '113'])).
% 2.04/2.25  thf('252', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['250', '251'])).
% 2.04/2.25  thf('253', plain,
% 2.04/2.25      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25         (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['252'])).
% 2.04/2.25  thf('254', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['249', '253'])).
% 2.04/2.25  thf('255', plain,
% 2.04/2.25      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25         (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['254'])).
% 2.04/2.25  thf('256', plain,
% 2.04/2.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ X11 @ X12 @ X13)
% 2.04/2.25          | ~ (r1_orders_2 @ X11 @ X13 @ (sk_D @ X13 @ X12 @ X11))
% 2.04/2.25          | ((X13) = (k1_yellow_0 @ X11 @ X12))
% 2.04/2.25          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 2.04/2.25          | ~ (r1_yellow_0 @ X11 @ X12)
% 2.04/2.25          | ~ (l1_orders_2 @ X11))),
% 2.04/2.25      inference('cnf', [status(esa)], [d9_yellow_0])).
% 2.04/2.25  thf('257', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.25      inference('sup-', [status(thm)], ['255', '256'])).
% 2.04/2.25  thf('258', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('259', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.25      inference('demod', [status(thm)], ['257', '258'])).
% 2.04/2.25  thf('260', plain,
% 2.04/2.25      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           sk_B)
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['259'])).
% 2.04/2.25  thf('261', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['232', '260'])).
% 2.04/2.25  thf('262', plain,
% 2.04/2.25      ((~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['261'])).
% 2.04/2.25  thf('263', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['231', '262'])).
% 2.04/2.25  thf('264', plain,
% 2.04/2.25      ((~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['263'])).
% 2.04/2.25  thf('265', plain,
% 2.04/2.25      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['15', '264'])).
% 2.04/2.25  thf('266', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('267', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.25      inference('demod', [status(thm)], ['265', '266'])).
% 2.04/2.25  thf('268', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | ~ (v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup+', [status(thm)], ['14', '267'])).
% 2.04/2.25  thf('269', plain, ((v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['182', '183'])).
% 2.04/2.25  thf('270', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('demod', [status(thm)], ['268', '269'])).
% 2.04/2.25  thf('271', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['270'])).
% 2.04/2.25  thf('272', plain,
% 2.04/2.25      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['13', '271'])).
% 2.04/2.25  thf('273', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('274', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('demod', [status(thm)], ['272', '273'])).
% 2.04/2.25  thf('275', plain,
% 2.04/2.25      (![X36 : $i]:
% 2.04/2.25         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X36) @ sk_A @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('276', plain,
% 2.04/2.25      (((v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E @ sk_A)) @ sk_A @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['274', '275'])).
% 2.04/2.25  thf('277', plain,
% 2.04/2.25      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.04/2.25         ((v2_struct_0 @ X27)
% 2.04/2.25          | ~ (v4_orders_2 @ X27)
% 2.04/2.25          | ~ (v7_waybel_0 @ X27)
% 2.04/2.25          | ~ (l1_waybel_0 @ X27 @ X28)
% 2.04/2.25          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 2.04/2.25          | (r2_lattice3 @ X28 @ 
% 2.04/2.25             (k2_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28) @ 
% 2.04/2.25              (u1_waybel_0 @ X28 @ X27)) @ 
% 2.04/2.25             X29)
% 2.04/2.25          | ((X30) != (X29))
% 2.04/2.25          | ~ (r3_waybel_9 @ X28 @ X27 @ X30)
% 2.04/2.25          | ~ (v10_waybel_0 @ X27 @ X28)
% 2.04/2.25          | ~ (v5_pre_topc @ (k4_waybel_1 @ X28 @ (sk_E @ X28)) @ X28 @ X28)
% 2.04/2.25          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 2.04/2.25          | ~ (l1_waybel_9 @ X28)
% 2.04/2.25          | ~ (v1_compts_1 @ X28)
% 2.04/2.25          | ~ (v2_lattice3 @ X28)
% 2.04/2.25          | ~ (v1_lattice3 @ X28)
% 2.04/2.25          | ~ (v5_orders_2 @ X28)
% 2.04/2.25          | ~ (v4_orders_2 @ X28)
% 2.04/2.25          | ~ (v3_orders_2 @ X28)
% 2.04/2.25          | ~ (v8_pre_topc @ X28)
% 2.04/2.25          | ~ (v2_pre_topc @ X28))),
% 2.04/2.25      inference('cnf', [status(esa)], [l48_waybel_9])).
% 2.04/2.25  thf('278', plain,
% 2.04/2.25      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.04/2.25         (~ (v2_pre_topc @ X28)
% 2.04/2.25          | ~ (v8_pre_topc @ X28)
% 2.04/2.25          | ~ (v3_orders_2 @ X28)
% 2.04/2.25          | ~ (v4_orders_2 @ X28)
% 2.04/2.25          | ~ (v5_orders_2 @ X28)
% 2.04/2.25          | ~ (v1_lattice3 @ X28)
% 2.04/2.25          | ~ (v2_lattice3 @ X28)
% 2.04/2.25          | ~ (v1_compts_1 @ X28)
% 2.04/2.25          | ~ (l1_waybel_9 @ X28)
% 2.04/2.25          | ~ (v5_pre_topc @ (k4_waybel_1 @ X28 @ (sk_E @ X28)) @ X28 @ X28)
% 2.04/2.25          | ~ (v10_waybel_0 @ X27 @ X28)
% 2.04/2.25          | ~ (r3_waybel_9 @ X28 @ X27 @ X29)
% 2.04/2.25          | (r2_lattice3 @ X28 @ 
% 2.04/2.25             (k2_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28) @ 
% 2.04/2.25              (u1_waybel_0 @ X28 @ X27)) @ 
% 2.04/2.25             X29)
% 2.04/2.25          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 2.04/2.25          | ~ (l1_waybel_0 @ X27 @ X28)
% 2.04/2.25          | ~ (v7_waybel_0 @ X27)
% 2.04/2.25          | ~ (v4_orders_2 @ X27)
% 2.04/2.25          | (v2_struct_0 @ X27))),
% 2.04/2.25      inference('simplify', [status(thm)], ['277'])).
% 2.04/2.25  thf('279', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ X0)
% 2.04/2.25          | ~ (v4_orders_2 @ X0)
% 2.04/2.25          | ~ (v7_waybel_0 @ X0)
% 2.04/2.25          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25              (u1_waybel_0 @ sk_A @ X0)) @ 
% 2.04/2.25             X1)
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 2.04/2.25          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 2.04/2.25          | ~ (l1_waybel_9 @ sk_A)
% 2.04/2.25          | ~ (v1_compts_1 @ sk_A)
% 2.04/2.25          | ~ (v2_lattice3 @ sk_A)
% 2.04/2.25          | ~ (v1_lattice3 @ sk_A)
% 2.04/2.25          | ~ (v5_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v4_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v3_orders_2 @ sk_A)
% 2.04/2.25          | ~ (v8_pre_topc @ sk_A)
% 2.04/2.25          | ~ (v2_pre_topc @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['276', '278'])).
% 2.04/2.25  thf('280', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('281', plain, ((v1_compts_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('282', plain, ((v2_lattice3 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('283', plain, ((v1_lattice3 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('284', plain, ((v5_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('285', plain, ((v4_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('286', plain, ((v3_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('287', plain, ((v8_pre_topc @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('288', plain, ((v2_pre_topc @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('289', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ X0)
% 2.04/2.25          | ~ (v4_orders_2 @ X0)
% 2.04/2.25          | ~ (v7_waybel_0 @ X0)
% 2.04/2.25          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25              (u1_waybel_0 @ sk_A @ X0)) @ 
% 2.04/2.25             X1)
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 2.04/2.25          | ~ (v10_waybel_0 @ X0 @ sk_A))),
% 2.04/2.25      inference('demod', [status(thm)],
% 2.04/2.25                ['279', '280', '281', '282', '283', '284', '285', '286', 
% 2.04/2.25                 '287', '288'])).
% 2.04/2.25  thf('290', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (v10_waybel_0 @ X0 @ sk_A)
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25              (u1_waybel_0 @ sk_A @ X0)) @ 
% 2.04/2.25             sk_B)
% 2.04/2.25          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 2.04/2.25          | ~ (v7_waybel_0 @ X0)
% 2.04/2.25          | ~ (v4_orders_2 @ X0)
% 2.04/2.25          | (v2_struct_0 @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['12', '289'])).
% 2.04/2.25  thf('291', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | ~ (v4_orders_2 @ sk_C_1)
% 2.04/2.25        | ~ (v7_waybel_0 @ sk_C_1)
% 2.04/2.25        | ~ (l1_waybel_0 @ sk_C_1 @ sk_A)
% 2.04/2.25        | (r2_lattice3 @ sk_A @ 
% 2.04/2.25           (k2_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25            (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           sk_B)
% 2.04/2.25        | ~ (v10_waybel_0 @ sk_C_1 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['11', '290'])).
% 2.04/2.25  thf('292', plain, ((v4_orders_2 @ sk_C_1)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('293', plain, ((v7_waybel_0 @ sk_C_1)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('294', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('295', plain,
% 2.04/2.25      (((k2_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 2.04/2.25         (u1_waybel_0 @ sk_A @ sk_C_1))
% 2.04/2.25         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['42', '43'])).
% 2.04/2.25  thf('296', plain, ((v10_waybel_0 @ sk_C_1 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('297', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           sk_B))),
% 2.04/2.25      inference('demod', [status(thm)],
% 2.04/2.25                ['291', '292', '293', '294', '295', '296'])).
% 2.04/2.25  thf('298', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['297'])).
% 2.04/2.25  thf('299', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('300', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['297'])).
% 2.04/2.25  thf('301', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((m1_subset_1 @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['59', '60'])).
% 2.04/2.25  thf('302', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['300', '301'])).
% 2.04/2.25  thf('303', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['297'])).
% 2.04/2.25  thf('304', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((r2_lattice3 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ X0 @ sk_A))
% 2.04/2.25          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['70', '71'])).
% 2.04/2.25  thf('305', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['303', '304'])).
% 2.04/2.25  thf('306', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('307', plain,
% 2.04/2.25      (![X24 : $i, X25 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X24)
% 2.04/2.25          | ((k4_yellow_2 @ X25 @ X24)
% 2.04/2.25              = (k1_yellow_0 @ X25 @ (k2_relat_1 @ X24)))
% 2.04/2.25          | ~ (l1_orders_2 @ X25)
% 2.04/2.25          | (v2_struct_0 @ X25))),
% 2.04/2.25      inference('cnf', [status(esa)], [d5_yellow_2])).
% 2.04/2.25  thf('308', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('309', plain,
% 2.04/2.25      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.25  thf('310', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['297'])).
% 2.04/2.25  thf('311', plain, ((r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('312', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['300', '301'])).
% 2.04/2.25  thf('313', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['303', '304'])).
% 2.04/2.25  thf('314', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X0)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X1)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)],
% 2.04/2.25                ['85', '86', '87', '88', '89', '90', '91', '92', '93', '94', 
% 2.04/2.25                 '95', '96', '97'])).
% 2.04/2.25  thf('315', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | ~ (m1_subset_1 @ 
% 2.04/2.25               (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25                sk_A) @ 
% 2.04/2.25               (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['313', '314'])).
% 2.04/2.25  thf('316', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ 
% 2.04/2.25               (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25                sk_A) @ 
% 2.04/2.25               (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['315'])).
% 2.04/2.25  thf('317', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['312', '316'])).
% 2.04/2.25  thf('318', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.25          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25          | (v2_struct_0 @ sk_A)
% 2.04/2.25          | (v2_struct_0 @ sk_C_1)
% 2.04/2.25          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['317'])).
% 2.04/2.25  thf('319', plain,
% 2.04/2.25      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['311', '318'])).
% 2.04/2.25  thf('320', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('321', plain,
% 2.04/2.25      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('demod', [status(thm)], ['319', '320'])).
% 2.04/2.25  thf('322', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['300', '301'])).
% 2.04/2.25  thf('323', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         ((v2_struct_0 @ sk_A)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.25          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['112', '113'])).
% 2.04/2.25  thf('324', plain,
% 2.04/2.25      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['322', '323'])).
% 2.04/2.25  thf('325', plain,
% 2.04/2.25      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25         (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25              sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['324'])).
% 2.04/2.25  thf('326', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['321', '325'])).
% 2.04/2.25  thf('327', plain,
% 2.04/2.25      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.25         (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['326'])).
% 2.04/2.25  thf('328', plain,
% 2.04/2.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.04/2.25         (~ (r1_orders_2 @ X17 @ X15 @ (sk_D_1 @ X15 @ X16 @ X17))
% 2.04/2.25          | ~ (r2_lattice3 @ X17 @ X16 @ X15)
% 2.04/2.25          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X17))
% 2.04/2.25          | (r1_yellow_0 @ X17 @ X16)
% 2.04/2.25          | ~ (l1_orders_2 @ X17)
% 2.04/2.25          | ~ (v5_orders_2 @ X17))),
% 2.04/2.25      inference('cnf', [status(esa)], [t15_yellow_0])).
% 2.04/2.25  thf('329', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (v5_orders_2 @ sk_A)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.25      inference('sup-', [status(thm)], ['327', '328'])).
% 2.04/2.25  thf('330', plain, ((v5_orders_2 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('331', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('332', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.25             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.25      inference('demod', [status(thm)], ['329', '330', '331'])).
% 2.04/2.25  thf('333', plain,
% 2.04/2.25      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25           sk_B)
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['332'])).
% 2.04/2.25  thf('334', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ~ (l1_orders_2 @ sk_A))),
% 2.04/2.25      inference('sup-', [status(thm)], ['310', '333'])).
% 2.04/2.25  thf('335', plain,
% 2.04/2.25      ((~ (l1_orders_2 @ sk_A)
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['334'])).
% 2.04/2.25  thf('336', plain,
% 2.04/2.25      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['309', '335'])).
% 2.04/2.25  thf('337', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('338', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('demod', [status(thm)], ['336', '337'])).
% 2.04/2.25  thf('339', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['297'])).
% 2.04/2.25  thf('340', plain, ((r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('341', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('demod', [status(thm)], ['336', '337'])).
% 2.04/2.25  thf('342', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['297'])).
% 2.04/2.25  thf('343', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.25          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25          | ((sk_B) = (k1_yellow_0 @ sk_A @ X0))
% 2.04/2.25          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['137', '138'])).
% 2.04/2.25  thf('344', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['342', '343'])).
% 2.04/2.25  thf('345', plain,
% 2.04/2.25      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B)
% 2.04/2.25            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.25               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['341', '344'])).
% 2.04/2.25  thf('346', plain,
% 2.04/2.25      ((((sk_B)
% 2.04/2.25          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.25        | (m1_subset_1 @ 
% 2.04/2.25           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.25           (u1_struct_0 @ sk_A))
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['345'])).
% 2.04/2.25  thf('347', plain,
% 2.04/2.25      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.25        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('demod', [status(thm)], ['336', '337'])).
% 2.04/2.25  thf('348', plain,
% 2.04/2.25      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.25         sk_B)
% 2.04/2.25        | (v2_struct_0 @ sk_C_1)
% 2.04/2.25        | (v2_struct_0 @ sk_A)
% 2.04/2.25        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.25      inference('simplify', [status(thm)], ['297'])).
% 2.04/2.25  thf('349', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.26         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.04/2.26          | (r2_lattice3 @ sk_A @ X0 @ (sk_D @ sk_B @ X0 @ sk_A))
% 2.04/2.26          | ((sk_B) = (k1_yellow_0 @ sk_A @ X0))
% 2.04/2.26          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 2.04/2.26      inference('demod', [status(thm)], ['149', '150'])).
% 2.04/2.26  thf('350', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['348', '349'])).
% 2.04/2.26  thf('351', plain,
% 2.04/2.26      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('sup-', [status(thm)], ['347', '350'])).
% 2.04/2.26  thf('352', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('simplify', [status(thm)], ['351'])).
% 2.04/2.26  thf('353', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X0)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X1)
% 2.04/2.26          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('demod', [status(thm)],
% 2.04/2.26                ['85', '86', '87', '88', '89', '90', '91', '92', '93', '94', 
% 2.04/2.26                 '95', '96', '97'])).
% 2.04/2.26  thf('354', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | ((sk_B)
% 2.04/2.26              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | ~ (m1_subset_1 @ 
% 2.04/2.26               (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26                sk_A) @ 
% 2.04/2.26               (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('sup-', [status(thm)], ['352', '353'])).
% 2.04/2.26  thf('355', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26          | ~ (m1_subset_1 @ 
% 2.04/2.26               (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26                sk_A) @ 
% 2.04/2.26               (u1_struct_0 @ sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | ((sk_B)
% 2.04/2.26              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('simplify', [status(thm)], ['354'])).
% 2.04/2.26  thf('356', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | ((sk_B)
% 2.04/2.26              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | ((sk_B)
% 2.04/2.26              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['346', '355'])).
% 2.04/2.26  thf('357', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | ((sk_B)
% 2.04/2.26              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('simplify', [status(thm)], ['356'])).
% 2.04/2.26  thf('358', plain,
% 2.04/2.26      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['340', '357'])).
% 2.04/2.26  thf('359', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('360', plain,
% 2.04/2.26      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.26      inference('demod', [status(thm)], ['358', '359'])).
% 2.04/2.26  thf('361', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (m1_subset_1 @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.26           (u1_struct_0 @ sk_A))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('simplify', [status(thm)], ['345'])).
% 2.04/2.26  thf('362', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.26          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('demod', [status(thm)], ['112', '113'])).
% 2.04/2.26  thf('363', plain,
% 2.04/2.26      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['361', '362'])).
% 2.04/2.26  thf('364', plain,
% 2.04/2.26      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26         (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('simplify', [status(thm)], ['363'])).
% 2.04/2.26  thf('365', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['360', '364'])).
% 2.04/2.26  thf('366', plain,
% 2.04/2.26      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26         (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['365'])).
% 2.04/2.26  thf('367', plain,
% 2.04/2.26      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.04/2.26         (~ (r2_lattice3 @ X11 @ X12 @ X13)
% 2.04/2.26          | ~ (r1_orders_2 @ X11 @ X13 @ (sk_D @ X13 @ X12 @ X11))
% 2.04/2.26          | ((X13) = (k1_yellow_0 @ X11 @ X12))
% 2.04/2.26          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 2.04/2.26          | ~ (r1_yellow_0 @ X11 @ X12)
% 2.04/2.26          | ~ (l1_orders_2 @ X11))),
% 2.04/2.26      inference('cnf', [status(esa)], [d9_yellow_0])).
% 2.04/2.26  thf('368', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.26      inference('sup-', [status(thm)], ['366', '367'])).
% 2.04/2.26  thf('369', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('370', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.26      inference('demod', [status(thm)], ['368', '369'])).
% 2.04/2.26  thf('371', plain,
% 2.04/2.26      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26           sk_B)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['370'])).
% 2.04/2.26  thf('372', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('sup-', [status(thm)], ['339', '371'])).
% 2.04/2.26  thf('373', plain,
% 2.04/2.26      ((~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['372'])).
% 2.04/2.26  thf('374', plain,
% 2.04/2.26      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['338', '373'])).
% 2.04/2.26  thf('375', plain,
% 2.04/2.26      ((~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('simplify', [status(thm)], ['374'])).
% 2.04/2.26  thf('376', plain,
% 2.04/2.26      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.26      inference('sup-', [status(thm)], ['308', '375'])).
% 2.04/2.26  thf('377', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('378', plain,
% 2.04/2.26      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.26      inference('demod', [status(thm)], ['376', '377'])).
% 2.04/2.26  thf('379', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ~ (v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('sup+', [status(thm)], ['307', '378'])).
% 2.04/2.26  thf('380', plain, ((v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))),
% 2.04/2.26      inference('sup-', [status(thm)], ['182', '183'])).
% 2.04/2.26  thf('381', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('demod', [status(thm)], ['379', '380'])).
% 2.04/2.26  thf('382', plain,
% 2.04/2.26      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['381'])).
% 2.04/2.26  thf('383', plain,
% 2.04/2.26      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['306', '382'])).
% 2.04/2.26  thf('384', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('385', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('demod', [status(thm)], ['383', '384'])).
% 2.04/2.26  thf('386', plain,
% 2.04/2.26      (![X36 : $i]:
% 2.04/2.26         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X36) @ sk_A @ sk_A)
% 2.04/2.26          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('387', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['385', '386'])).
% 2.04/2.26  thf('388', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X0)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X1)
% 2.04/2.26          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 2.04/2.26               sk_A))),
% 2.04/2.26      inference('demod', [status(thm)],
% 2.04/2.26                ['195', '196', '197', '198', '199', '200', '201', '202', 
% 2.04/2.26                 '203', '204', '205', '206', '207'])).
% 2.04/2.26  thf('389', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         (((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ X1)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X1))),
% 2.04/2.26      inference('sup-', [status(thm)], ['387', '388'])).
% 2.04/2.26  thf('390', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X1)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ X1)
% 2.04/2.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['389'])).
% 2.04/2.26  thf('391', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | ~ (m1_subset_1 @ 
% 2.04/2.26               (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26                sk_A) @ 
% 2.04/2.26               (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26              sk_A))
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['305', '390'])).
% 2.04/2.26  thf('392', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26              sk_A))
% 2.04/2.26          | ~ (m1_subset_1 @ 
% 2.04/2.26               (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26                sk_A) @ 
% 2.04/2.26               (u1_struct_0 @ sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['391'])).
% 2.04/2.26  thf('393', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26              sk_A))
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['302', '392'])).
% 2.04/2.26  thf('394', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26              sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['393'])).
% 2.04/2.26  thf('395', plain,
% 2.04/2.26      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)
% 2.04/2.26        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['299', '394'])).
% 2.04/2.26  thf('396', plain, ((r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('397', plain,
% 2.04/2.26      (((r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.26      inference('demod', [status(thm)], ['395', '396'])).
% 2.04/2.26  thf('398', plain,
% 2.04/2.26      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26         (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26             (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26              sk_A))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['324'])).
% 2.04/2.26  thf('399', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['397', '398'])).
% 2.04/2.26  thf('400', plain,
% 2.04/2.26      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26         (sk_D_1 @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['399'])).
% 2.04/2.26  thf('401', plain,
% 2.04/2.26      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.04/2.26         (~ (r1_orders_2 @ X17 @ X15 @ (sk_D_1 @ X15 @ X16 @ X17))
% 2.04/2.26          | ~ (r2_lattice3 @ X17 @ X16 @ X15)
% 2.04/2.26          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X17))
% 2.04/2.26          | (r1_yellow_0 @ X17 @ X16)
% 2.04/2.26          | ~ (l1_orders_2 @ X17)
% 2.04/2.26          | ~ (v5_orders_2 @ X17))),
% 2.04/2.26      inference('cnf', [status(esa)], [t15_yellow_0])).
% 2.04/2.26  thf('402', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (v5_orders_2 @ sk_A)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.26      inference('sup-', [status(thm)], ['400', '401'])).
% 2.04/2.26  thf('403', plain, ((v5_orders_2 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('404', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('405', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.26      inference('demod', [status(thm)], ['402', '403', '404'])).
% 2.04/2.26  thf('406', plain,
% 2.04/2.26      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26           sk_B)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['405'])).
% 2.04/2.26  thf('407', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['298', '406'])).
% 2.04/2.26  thf('408', plain,
% 2.04/2.26      ((~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['407'])).
% 2.04/2.26  thf('409', plain,
% 2.04/2.26      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('sup-', [status(thm)], ['10', '408'])).
% 2.04/2.26  thf('410', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('411', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('demod', [status(thm)], ['409', '410'])).
% 2.04/2.26  thf('412', plain,
% 2.04/2.26      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26         sk_B)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['297'])).
% 2.04/2.26  thf('413', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('414', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('demod', [status(thm)], ['409', '410'])).
% 2.04/2.26  thf('415', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (m1_subset_1 @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.26           (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['342', '343'])).
% 2.04/2.26  thf('416', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (m1_subset_1 @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.26           (u1_struct_0 @ sk_A))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('sup-', [status(thm)], ['414', '415'])).
% 2.04/2.26  thf('417', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (m1_subset_1 @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.26           (u1_struct_0 @ sk_A))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('simplify', [status(thm)], ['416'])).
% 2.04/2.26  thf('418', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('demod', [status(thm)], ['409', '410'])).
% 2.04/2.26  thf('419', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['348', '349'])).
% 2.04/2.26  thf('420', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('sup-', [status(thm)], ['418', '419'])).
% 2.04/2.26  thf('421', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('simplify', [status(thm)], ['420'])).
% 2.04/2.26  thf('422', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         (~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ X1)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ X1)
% 2.04/2.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['389'])).
% 2.04/2.26  thf('423', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | ((sk_B)
% 2.04/2.26              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | ~ (m1_subset_1 @ 
% 2.04/2.26               (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26                sk_A) @ 
% 2.04/2.26               (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['421', '422'])).
% 2.04/2.26  thf('424', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26          | ~ (m1_subset_1 @ 
% 2.04/2.26               (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26                sk_A) @ 
% 2.04/2.26               (u1_struct_0 @ sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | ((sk_B)
% 2.04/2.26              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('simplify', [status(thm)], ['423'])).
% 2.04/2.26  thf('425', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | ((sk_B)
% 2.04/2.26              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26          | (v2_struct_0 @ sk_C_1)
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | ((sk_B)
% 2.04/2.26              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['417', '424'])).
% 2.04/2.26  thf('426', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r3_orders_2 @ sk_A @ X0 @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26          | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ X0)
% 2.04/2.26          | ((sk_B)
% 2.04/2.26              = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26          | (v2_struct_0 @ sk_A)
% 2.04/2.26          | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('simplify', [status(thm)], ['425'])).
% 2.04/2.26  thf('427', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ~ (r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)
% 2.04/2.26        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['413', '426'])).
% 2.04/2.26  thf('428', plain, ((r3_waybel_9 @ sk_A @ sk_C_1 @ sk_B)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('429', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.26      inference('demod', [status(thm)], ['427', '428'])).
% 2.04/2.26  thf('430', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (m1_subset_1 @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 2.04/2.26           (u1_struct_0 @ sk_A))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('simplify', [status(thm)], ['416'])).
% 2.04/2.26  thf('431', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.04/2.26          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('demod', [status(thm)], ['112', '113'])).
% 2.04/2.26  thf('432', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['430', '431'])).
% 2.04/2.26  thf('433', plain,
% 2.04/2.26      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26         (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26             (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('simplify', [status(thm)], ['432'])).
% 2.04/2.26  thf('434', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26           (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['429', '433'])).
% 2.04/2.26  thf('435', plain,
% 2.04/2.26      (((r1_orders_2 @ sk_A @ sk_B @ 
% 2.04/2.26         (sk_D @ sk_B @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['434'])).
% 2.04/2.26  thf('436', plain,
% 2.04/2.26      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.04/2.26         (~ (r2_lattice3 @ X11 @ X12 @ X13)
% 2.04/2.26          | ~ (r1_orders_2 @ X11 @ X13 @ (sk_D @ X13 @ X12 @ X11))
% 2.04/2.26          | ((X13) = (k1_yellow_0 @ X11 @ X12))
% 2.04/2.26          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 2.04/2.26          | ~ (r1_yellow_0 @ X11 @ X12)
% 2.04/2.26          | ~ (l1_orders_2 @ X11))),
% 2.04/2.26      inference('cnf', [status(esa)], [d9_yellow_0])).
% 2.04/2.26  thf('437', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.26      inference('sup-', [status(thm)], ['435', '436'])).
% 2.04/2.26  thf('438', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('439', plain,
% 2.04/2.26      ((((sk_B)
% 2.04/2.26          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ~ (r2_lattice3 @ sk_A @ 
% 2.04/2.26             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 2.04/2.26      inference('demod', [status(thm)], ['437', '438'])).
% 2.04/2.26  thf('440', plain,
% 2.04/2.26      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)) @ 
% 2.04/2.26           sk_B)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['439'])).
% 2.04/2.26  thf('441', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('sup-', [status(thm)], ['412', '440'])).
% 2.04/2.26  thf('442', plain,
% 2.04/2.26      ((~ (r1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['441'])).
% 2.04/2.26  thf('443', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['411', '442'])).
% 2.04/2.26  thf('444', plain,
% 2.04/2.26      ((~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('simplify', [status(thm)], ['443'])).
% 2.04/2.26  thf('445', plain,
% 2.04/2.26      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.26      inference('sup-', [status(thm)], ['9', '444'])).
% 2.04/2.26  thf('446', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('447', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_C_1)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | ((sk_B)
% 2.04/2.26            = (k1_yellow_0 @ sk_A @ 
% 2.04/2.26               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1)))))),
% 2.04/2.26      inference('demod', [status(thm)], ['445', '446'])).
% 2.04/2.26  thf('448', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ~ (v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('sup+', [status(thm)], ['8', '447'])).
% 2.04/2.26  thf('449', plain, ((v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C_1))),
% 2.04/2.26      inference('sup-', [status(thm)], ['182', '183'])).
% 2.04/2.26  thf('450', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('demod', [status(thm)], ['448', '449'])).
% 2.04/2.26  thf('451', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_C_1)
% 2.04/2.26        | ~ (l1_orders_2 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('simplify', [status(thm)], ['450'])).
% 2.04/2.26  thf('452', plain,
% 2.04/2.26      ((~ (l1_waybel_9 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('sup-', [status(thm)], ['7', '451'])).
% 2.04/2.26  thf('453', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('454', plain,
% 2.04/2.26      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1)))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.04/2.26      inference('demod', [status(thm)], ['452', '453'])).
% 2.04/2.26  thf('455', plain, (~ (v2_struct_0 @ sk_C_1)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('456', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_A)
% 2.04/2.26        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C_1))))),
% 2.04/2.26      inference('clc', [status(thm)], ['454', '455'])).
% 2.04/2.26  thf('457', plain,
% 2.04/2.26      ((((sk_B) = (k1_waybel_2 @ sk_A @ sk_C_1))
% 2.04/2.26        | (v2_struct_0 @ sk_A)
% 2.04/2.26        | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('sup+', [status(thm)], ['6', '456'])).
% 2.04/2.26  thf('458', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_A) | ((sk_B) = (k1_waybel_2 @ sk_A @ sk_C_1)))),
% 2.04/2.26      inference('simplify', [status(thm)], ['457'])).
% 2.04/2.26  thf('459', plain, (((sk_B) != (k1_waybel_2 @ sk_A @ sk_C_1))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('460', plain, ((v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('simplify_reflect-', [status(thm)], ['458', '459'])).
% 2.04/2.26  thf('461', plain,
% 2.04/2.26      (![X26 : $i]: ((l1_orders_2 @ X26) | ~ (l1_waybel_9 @ X26))),
% 2.04/2.26      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 2.04/2.26  thf(cc1_lattice3, axiom,
% 2.04/2.26    (![A:$i]:
% 2.04/2.26     ( ( l1_orders_2 @ A ) =>
% 2.04/2.26       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 2.04/2.26  thf('462', plain,
% 2.04/2.26      (![X10 : $i]:
% 2.04/2.26         (~ (v1_lattice3 @ X10) | ~ (v2_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 2.04/2.26      inference('cnf', [status(esa)], [cc1_lattice3])).
% 2.04/2.26  thf('463', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v1_lattice3 @ X0))),
% 2.04/2.26      inference('sup-', [status(thm)], ['461', '462'])).
% 2.04/2.26  thf('464', plain, ((~ (v1_lattice3 @ sk_A) | ~ (l1_waybel_9 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['460', '463'])).
% 2.04/2.26  thf('465', plain, ((v1_lattice3 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('466', plain, ((l1_waybel_9 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('467', plain, ($false),
% 2.04/2.26      inference('demod', [status(thm)], ['464', '465', '466'])).
% 2.04/2.26  
% 2.04/2.26  % SZS output end Refutation
% 2.04/2.26  
% 2.04/2.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
