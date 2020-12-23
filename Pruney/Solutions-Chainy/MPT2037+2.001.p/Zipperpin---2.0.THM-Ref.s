%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Eijiy9U4i

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:35 EST 2020

% Result     : Theorem 5.83s
% Output     : Refutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :  316 (3637 expanded)
%              Number of leaves         :   63 (1111 expanded)
%              Depth                    :   87
%              Number of atoms          : 4459 (109146 expanded)
%              Number of equality atoms :  107 (1926 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(k1_waybel_9_type,type,(
    k1_waybel_9: $i > $i > $i )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k5_yellow_2_type,type,(
    k5_yellow_2: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v11_waybel_0_type,type,(
    v11_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X30: $i] :
      ( ( l1_orders_2 @ X30 )
      | ~ ( l1_waybel_9 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('1',plain,(
    ! [X30: $i] :
      ( ( l1_orders_2 @ X30 )
      | ~ ( l1_waybel_9 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(t36_waybel_9,conjecture,(
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
                  & ( v11_waybel_0 @ C @ A )
                  & ( r3_waybel_9 @ A @ C @ B ) )
               => ( B
                  = ( k1_waybel_9 @ A @ C ) ) ) ) ) ) )).

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
                    & ( v11_waybel_0 @ C @ A )
                    & ( r3_waybel_9 @ A @ C @ B ) )
                 => ( B
                    = ( k1_waybel_9 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_waybel_9])).

thf('2',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( k1_waybel_9 @ A @ B )
            = ( k5_yellow_2 @ A @ ( u1_waybel_0 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_waybel_0 @ X26 @ X27 )
      | ( ( k1_waybel_9 @ X27 @ X26 )
        = ( k5_yellow_2 @ X27 @ ( u1_waybel_0 @ X27 @ X26 ) ) )
      | ~ ( l1_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_waybel_9])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_waybel_9 @ sk_A @ sk_C )
      = ( k5_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k1_waybel_9 @ sk_A @ sk_C )
      = ( k5_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_waybel_9 @ sk_A @ sk_C )
      = ( k5_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X30: $i] :
      ( ( l1_orders_2 @ X30 )
      | ~ ( l1_waybel_9 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(d6_yellow_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k5_yellow_2 @ A @ B )
            = ( k2_yellow_0 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( ( k5_yellow_2 @ X29 @ X28 )
        = ( k2_yellow_0 @ X29 @ ( k2_relat_1 @ X28 ) ) )
      | ~ ( l1_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d6_yellow_2])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ~ ( v1_lattice3 @ X7 )
      | ~ ( v2_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k5_yellow_2 @ X0 @ X1 )
        = ( k2_yellow_0 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_yellow_2 @ X0 @ X1 )
        = ( k2_yellow_0 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ( ( k5_yellow_2 @ X0 @ X1 )
        = ( k2_yellow_0 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_waybel_9,axiom,(
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
                      & ( v11_waybel_0 @ B @ A )
                      & ( r3_waybel_9 @ A @ B @ C ) )
                   => ( r1_lattice3 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) @ D ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( r1_lattice3 @ X32 @ ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) @ ( u1_waybel_0 @ X32 @ X31 ) ) @ X33 )
      | ( X34 != X33 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X34 )
      | ~ ( v11_waybel_0 @ X31 @ X32 )
      | ( m1_subset_1 @ ( sk_E @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_waybel_9 @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( v2_lattice3 @ X32 )
      | ~ ( v1_lattice3 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_waybel_9])).

thf('19',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_pre_topc @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v1_lattice3 @ X32 )
      | ~ ( v2_lattice3 @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( l1_waybel_9 @ X32 )
      | ( m1_subset_1 @ ( sk_E @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v11_waybel_0 @ X31 @ X32 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X33 )
      | ( r1_lattice3 @ X32 @ ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) @ ( u1_waybel_0 @ X32 @ X31 ) ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_B )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
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
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_B )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25','26','27','28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v11_waybel_0 @ sk_C @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( v7_waybel_0 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,(
    v11_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X24 )
      | ~ ( l1_waybel_0 @ X25 @ X24 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X30: $i] :
      ( ( l1_orders_2 @ X30 )
      | ~ ( l1_waybel_9 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('38',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k2_relset_1 @ X4 @ X5 @ X3 )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['31','32','43','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(t31_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_yellow_0 @ A @ C )
                  & ( B
                    = ( k2_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) )
                  & ( r1_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) )
                  & ( r1_lattice3 @ A @ C @ B ) )
               => ( ( r2_yellow_0 @ A @ C )
                  & ( B
                    = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r1_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ D @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( r1_lattice3 @ X11 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('54',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('55',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( r1_lattice3 @ X11 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(l52_waybel_9,axiom,(
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
                       => ( ( r1_lattice3 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) @ E )
                         => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v7_waybel_0 @ X35 )
      | ~ ( l1_waybel_0 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_lattice3 @ X36 @ ( k2_relset_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X36 ) @ ( u1_waybel_0 @ X36 @ X35 ) ) @ X38 )
      | ( r1_orders_2 @ X36 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ( X39 != X37 )
      | ~ ( r3_waybel_9 @ X36 @ X35 @ X39 )
      | ( m1_subset_1 @ ( sk_E_1 @ X36 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_waybel_9 @ X36 )
      | ~ ( v1_compts_1 @ X36 )
      | ~ ( v2_lattice3 @ X36 )
      | ~ ( v1_lattice3 @ X36 )
      | ~ ( v5_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ~ ( v8_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[l52_waybel_9])).

thf('61',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_pre_topc @ X36 )
      | ~ ( v8_pre_topc @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v5_orders_2 @ X36 )
      | ~ ( v1_lattice3 @ X36 )
      | ~ ( v2_lattice3 @ X36 )
      | ~ ( v1_compts_1 @ X36 )
      | ~ ( l1_waybel_9 @ X36 )
      | ( m1_subset_1 @ ( sk_E_1 @ X36 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( r3_waybel_9 @ X36 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ( r1_orders_2 @ X36 @ X38 @ X37 )
      | ~ ( r1_lattice3 @ X36 @ ( k2_relset_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X36 ) @ ( u1_waybel_0 @ X36 @ X35 ) ) @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_waybel_0 @ X35 @ X36 )
      | ~ ( v7_waybel_0 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_C )
      | ~ ( v7_waybel_0 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
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
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66','67','68','69','70','71','72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X2 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','79'])).

thf('81',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(eq_fact,[status(thm)],['82'])).

thf('84',plain,(
    ! [X30: $i] :
      ( ( l1_orders_2 @ X30 )
      | ~ ( l1_waybel_9 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k2_yellow_0 @ A @ C ) )
        & ( r2_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k2_yellow_0 @ A @ C ) )
                  & ( r2_yellow_0 @ A @ C ) )
               => ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) )).

thf('86',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_lattice3 @ X20 @ X23 @ X19 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 @ X19 @ X20 )
      | ( zip_tseitin_2 @ X23 @ X19 @ X20 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['83','92'])).

thf('94',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','93'])).

thf('95',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( r1_orders_2 @ X11 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','101'])).

thf('103',plain,
    ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k2_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('105',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('109',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v7_waybel_0 @ X35 )
      | ~ ( l1_waybel_0 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_lattice3 @ X36 @ ( k2_relset_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X36 ) @ ( u1_waybel_0 @ X36 @ X35 ) ) @ X38 )
      | ( r1_orders_2 @ X36 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ( X39 != X37 )
      | ~ ( r3_waybel_9 @ X36 @ X35 @ X39 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X36 @ ( sk_E_1 @ X36 ) ) @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_waybel_9 @ X36 )
      | ~ ( v1_compts_1 @ X36 )
      | ~ ( v2_lattice3 @ X36 )
      | ~ ( v1_lattice3 @ X36 )
      | ~ ( v5_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ~ ( v8_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[l52_waybel_9])).

thf('110',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_pre_topc @ X36 )
      | ~ ( v8_pre_topc @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v5_orders_2 @ X36 )
      | ~ ( v1_lattice3 @ X36 )
      | ~ ( v2_lattice3 @ X36 )
      | ~ ( v1_compts_1 @ X36 )
      | ~ ( l1_waybel_9 @ X36 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X36 @ ( sk_E_1 @ X36 ) ) @ X36 @ X36 )
      | ~ ( r3_waybel_9 @ X36 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ( r1_orders_2 @ X36 @ X38 @ X37 )
      | ~ ( r1_lattice3 @ X36 @ ( k2_relset_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X36 ) @ ( u1_waybel_0 @ X36 @ X35 ) ) @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_waybel_0 @ X35 @ X36 )
      | ~ ( v7_waybel_0 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_C )
      | ~ ( v7_waybel_0 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
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
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116','117','118','119','120','121','122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['107','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X2 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','130'])).

thf('132',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('136',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['50','136'])).

thf('138',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( r1_orders_2 @ X11 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('144',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['49','145'])).

thf('147',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k2_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('149',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( r1_lattice3 @ X32 @ ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) @ ( u1_waybel_0 @ X32 @ X31 ) ) @ X33 )
      | ( X34 != X33 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X34 )
      | ~ ( v11_waybel_0 @ X31 @ X32 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X32 @ ( sk_E @ X32 ) ) @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_waybel_9 @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( v2_lattice3 @ X32 )
      | ~ ( v1_lattice3 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_waybel_9])).

thf('156',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_pre_topc @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v1_lattice3 @ X32 )
      | ~ ( v2_lattice3 @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( l1_waybel_9 @ X32 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X32 @ ( sk_E @ X32 ) ) @ X32 @ X32 )
      | ~ ( v11_waybel_0 @ X31 @ X32 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X33 )
      | ( r1_lattice3 @ X32 @ ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) @ ( u1_waybel_0 @ X32 @ X31 ) ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','156'])).

thf('158',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v11_waybel_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158','159','160','161','162','163','164','165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_B )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','167'])).

thf('169',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ~ ( v7_waybel_0 @ sk_C )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ~ ( v11_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['14','168'])).

thf('170',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('174',plain,(
    v11_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['169','170','171','172','173','174'])).

thf('176',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('179',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('180',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k2_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('185',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( r1_lattice3 @ X11 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('188',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('189',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['83','92'])).

thf('191',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( r1_orders_2 @ X11 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['188','198'])).

thf('200',plain,
    ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k2_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('202',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116','117','118','119','120','121','122','123'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X2 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['187','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['186','210'])).

thf('212',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['185','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('219',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['178','219'])).

thf('221',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( r1_orders_2 @ X11 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('227',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['177','228'])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k2_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('234',plain,
    ( sk_B
    = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( sk_B
      = ( k5_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','234'])).

thf('236',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('238',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('239',plain,(
    v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( sk_B
    = ( k5_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['235','236','239','240'])).

thf('242',plain,
    ( ( sk_B
      = ( k1_waybel_9 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','241'])).

thf('243',plain,(
    sk_B
 != ( k1_waybel_9 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X7: $i] :
      ( ~ ( v1_lattice3 @ X7 )
      | ~ ( v2_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('246',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','248'])).

thf('250',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    $false ),
    inference(demod,[status(thm)],['249','250'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Eijiy9U4i
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 5.83/6.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.83/6.09  % Solved by: fo/fo7.sh
% 5.83/6.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.83/6.09  % done 2330 iterations in 5.616s
% 5.83/6.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.83/6.09  % SZS output start Refutation
% 5.83/6.09  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 5.83/6.09  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 5.83/6.09  thf(k1_waybel_9_type, type, k1_waybel_9: $i > $i > $i).
% 5.83/6.09  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 5.83/6.09  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.83/6.09  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 5.83/6.09  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 5.83/6.09  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 5.83/6.09  thf(sk_C_type, type, sk_C: $i).
% 5.83/6.09  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.83/6.09  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 5.83/6.09  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 5.83/6.09  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 5.83/6.09  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 5.83/6.09  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 5.83/6.09  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 5.83/6.09  thf(sk_E_type, type, sk_E: $i > $i).
% 5.83/6.09  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 5.83/6.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.83/6.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.83/6.09  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 5.83/6.09  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 5.83/6.09  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 5.83/6.09  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 5.83/6.09  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 5.83/6.09  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.83/6.09  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.83/6.09  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 5.83/6.09  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 5.83/6.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.83/6.09  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 5.83/6.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.83/6.09  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 5.83/6.09  thf(k5_yellow_2_type, type, k5_yellow_2: $i > $i > $i).
% 5.83/6.09  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.83/6.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.83/6.09  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 5.83/6.09  thf(v11_waybel_0_type, type, v11_waybel_0: $i > $i > $o).
% 5.83/6.09  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.83/6.09  thf(sk_B_type, type, sk_B: $i).
% 5.83/6.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.83/6.09  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.83/6.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.83/6.09  thf(sk_A_type, type, sk_A: $i).
% 5.83/6.09  thf(dt_l1_waybel_9, axiom,
% 5.83/6.09    (![A:$i]:
% 5.83/6.09     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 5.83/6.09  thf('0', plain, (![X30 : $i]: ((l1_orders_2 @ X30) | ~ (l1_waybel_9 @ X30))),
% 5.83/6.09      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 5.83/6.09  thf('1', plain, (![X30 : $i]: ((l1_orders_2 @ X30) | ~ (l1_waybel_9 @ X30))),
% 5.83/6.09      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 5.83/6.09  thf(t36_waybel_9, conjecture,
% 5.83/6.09    (![A:$i]:
% 5.83/6.09     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 5.83/6.09         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 5.83/6.09         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 5.83/6.09       ( ![B:$i]:
% 5.83/6.09         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.83/6.09           ( ![C:$i]:
% 5.83/6.09             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 5.83/6.09                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 5.83/6.09               ( ( ( ![D:$i]:
% 5.83/6.09                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.83/6.09                       ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 5.83/6.09                   ( v11_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 5.83/6.09                 ( ( B ) = ( k1_waybel_9 @ A @ C ) ) ) ) ) ) ) ))).
% 5.83/6.09  thf(zf_stmt_0, negated_conjecture,
% 5.83/6.09    (~( ![A:$i]:
% 5.83/6.09        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 5.83/6.09            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 5.83/6.09            ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 5.83/6.09          ( ![B:$i]:
% 5.83/6.09            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.83/6.09              ( ![C:$i]:
% 5.83/6.09                ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 5.83/6.09                    ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 5.83/6.09                  ( ( ( ![D:$i]:
% 5.83/6.09                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.83/6.09                          ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 5.83/6.09                      ( v11_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 5.83/6.09                    ( ( B ) = ( k1_waybel_9 @ A @ C ) ) ) ) ) ) ) ) )),
% 5.83/6.09    inference('cnf.neg', [status(esa)], [t36_waybel_9])).
% 5.83/6.09  thf('2', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf(d2_waybel_9, axiom,
% 5.83/6.09    (![A:$i]:
% 5.83/6.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 5.83/6.09       ( ![B:$i]:
% 5.83/6.09         ( ( l1_waybel_0 @ B @ A ) =>
% 5.83/6.09           ( ( k1_waybel_9 @ A @ B ) =
% 5.83/6.09             ( k5_yellow_2 @ A @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 5.83/6.09  thf('3', plain,
% 5.83/6.09      (![X26 : $i, X27 : $i]:
% 5.83/6.09         (~ (l1_waybel_0 @ X26 @ X27)
% 5.83/6.09          | ((k1_waybel_9 @ X27 @ X26)
% 5.83/6.09              = (k5_yellow_2 @ X27 @ (u1_waybel_0 @ X27 @ X26)))
% 5.83/6.09          | ~ (l1_orders_2 @ X27)
% 5.83/6.09          | (v2_struct_0 @ X27))),
% 5.83/6.09      inference('cnf', [status(esa)], [d2_waybel_9])).
% 5.83/6.09  thf('4', plain,
% 5.83/6.09      (((v2_struct_0 @ sk_A)
% 5.83/6.09        | ~ (l1_orders_2 @ sk_A)
% 5.83/6.09        | ((k1_waybel_9 @ sk_A @ sk_C)
% 5.83/6.09            = (k5_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C))))),
% 5.83/6.09      inference('sup-', [status(thm)], ['2', '3'])).
% 5.83/6.09  thf('5', plain,
% 5.83/6.09      ((~ (l1_waybel_9 @ sk_A)
% 5.83/6.09        | ((k1_waybel_9 @ sk_A @ sk_C)
% 5.83/6.09            = (k5_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 5.83/6.09        | (v2_struct_0 @ sk_A))),
% 5.83/6.09      inference('sup-', [status(thm)], ['1', '4'])).
% 5.83/6.09  thf('6', plain, ((l1_waybel_9 @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('7', plain,
% 5.83/6.09      ((((k1_waybel_9 @ sk_A @ sk_C)
% 5.83/6.09          = (k5_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 5.83/6.09        | (v2_struct_0 @ sk_A))),
% 5.83/6.09      inference('demod', [status(thm)], ['5', '6'])).
% 5.83/6.09  thf('8', plain, (![X30 : $i]: ((l1_orders_2 @ X30) | ~ (l1_waybel_9 @ X30))),
% 5.83/6.09      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 5.83/6.09  thf(d6_yellow_2, axiom,
% 5.83/6.09    (![A:$i]:
% 5.83/6.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 5.83/6.09       ( ![B:$i]:
% 5.83/6.09         ( ( v1_relat_1 @ B ) =>
% 5.83/6.09           ( ( k5_yellow_2 @ A @ B ) = ( k2_yellow_0 @ A @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 5.83/6.09  thf('9', plain,
% 5.83/6.09      (![X28 : $i, X29 : $i]:
% 5.83/6.09         (~ (v1_relat_1 @ X28)
% 5.83/6.09          | ((k5_yellow_2 @ X29 @ X28)
% 5.83/6.09              = (k2_yellow_0 @ X29 @ (k2_relat_1 @ X28)))
% 5.83/6.09          | ~ (l1_orders_2 @ X29)
% 5.83/6.09          | (v2_struct_0 @ X29))),
% 5.83/6.09      inference('cnf', [status(esa)], [d6_yellow_2])).
% 5.83/6.09  thf(cc1_lattice3, axiom,
% 5.83/6.09    (![A:$i]:
% 5.83/6.09     ( ( l1_orders_2 @ A ) =>
% 5.83/6.09       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 5.83/6.09  thf('10', plain,
% 5.83/6.09      (![X7 : $i]:
% 5.83/6.09         (~ (v1_lattice3 @ X7) | ~ (v2_struct_0 @ X7) | ~ (l1_orders_2 @ X7))),
% 5.83/6.09      inference('cnf', [status(esa)], [cc1_lattice3])).
% 5.83/6.09  thf('11', plain,
% 5.83/6.09      (![X0 : $i, X1 : $i]:
% 5.83/6.09         (~ (l1_orders_2 @ X0)
% 5.83/6.09          | ((k5_yellow_2 @ X0 @ X1) = (k2_yellow_0 @ X0 @ (k2_relat_1 @ X1)))
% 5.83/6.09          | ~ (v1_relat_1 @ X1)
% 5.83/6.09          | ~ (l1_orders_2 @ X0)
% 5.83/6.09          | ~ (v1_lattice3 @ X0))),
% 5.83/6.09      inference('sup-', [status(thm)], ['9', '10'])).
% 5.83/6.09  thf('12', plain,
% 5.83/6.09      (![X0 : $i, X1 : $i]:
% 5.83/6.09         (~ (v1_lattice3 @ X0)
% 5.83/6.09          | ~ (v1_relat_1 @ X1)
% 5.83/6.09          | ((k5_yellow_2 @ X0 @ X1) = (k2_yellow_0 @ X0 @ (k2_relat_1 @ X1)))
% 5.83/6.09          | ~ (l1_orders_2 @ X0))),
% 5.83/6.09      inference('simplify', [status(thm)], ['11'])).
% 5.83/6.09  thf('13', plain,
% 5.83/6.09      (![X0 : $i, X1 : $i]:
% 5.83/6.09         (~ (l1_waybel_9 @ X0)
% 5.83/6.09          | ((k5_yellow_2 @ X0 @ X1) = (k2_yellow_0 @ X0 @ (k2_relat_1 @ X1)))
% 5.83/6.09          | ~ (v1_relat_1 @ X1)
% 5.83/6.09          | ~ (v1_lattice3 @ X0))),
% 5.83/6.09      inference('sup-', [status(thm)], ['8', '12'])).
% 5.83/6.09  thf('14', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('16', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf(l51_waybel_9, axiom,
% 5.83/6.09    (![A:$i]:
% 5.83/6.09     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 5.83/6.09         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 5.83/6.09         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 5.83/6.09       ( ![B:$i]:
% 5.83/6.09         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 5.83/6.09             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 5.83/6.09           ( ![C:$i]:
% 5.83/6.09             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.83/6.09               ( ![D:$i]:
% 5.83/6.09                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.83/6.09                   ( ( ( ( C ) = ( D ) ) & 
% 5.83/6.09                       ( ![E:$i]:
% 5.83/6.09                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 5.83/6.09                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 5.83/6.09                       ( v11_waybel_0 @ B @ A ) & ( r3_waybel_9 @ A @ B @ C ) ) =>
% 5.83/6.09                     ( r1_lattice3 @
% 5.83/6.09                       A @ 
% 5.83/6.09                       ( k2_relset_1 @
% 5.83/6.09                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 5.83/6.09                         ( u1_waybel_0 @ A @ B ) ) @ 
% 5.83/6.09                       D ) ) ) ) ) ) ) ) ))).
% 5.83/6.09  thf('18', plain,
% 5.83/6.09      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 5.83/6.09         ((v2_struct_0 @ X31)
% 5.83/6.09          | ~ (v4_orders_2 @ X31)
% 5.83/6.09          | ~ (v7_waybel_0 @ X31)
% 5.83/6.09          | ~ (l1_waybel_0 @ X31 @ X32)
% 5.83/6.09          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 5.83/6.09          | (r1_lattice3 @ X32 @ 
% 5.83/6.09             (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 5.83/6.09              (u1_waybel_0 @ X32 @ X31)) @ 
% 5.83/6.09             X33)
% 5.83/6.09          | ((X34) != (X33))
% 5.83/6.09          | ~ (r3_waybel_9 @ X32 @ X31 @ X34)
% 5.83/6.09          | ~ (v11_waybel_0 @ X31 @ X32)
% 5.83/6.09          | (m1_subset_1 @ (sk_E @ X32) @ (u1_struct_0 @ X32))
% 5.83/6.09          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 5.83/6.09          | ~ (l1_waybel_9 @ X32)
% 5.83/6.09          | ~ (v1_compts_1 @ X32)
% 5.83/6.09          | ~ (v2_lattice3 @ X32)
% 5.83/6.09          | ~ (v1_lattice3 @ X32)
% 5.83/6.09          | ~ (v5_orders_2 @ X32)
% 5.83/6.09          | ~ (v4_orders_2 @ X32)
% 5.83/6.09          | ~ (v3_orders_2 @ X32)
% 5.83/6.09          | ~ (v8_pre_topc @ X32)
% 5.83/6.09          | ~ (v2_pre_topc @ X32))),
% 5.83/6.09      inference('cnf', [status(esa)], [l51_waybel_9])).
% 5.83/6.09  thf('19', plain,
% 5.83/6.09      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.83/6.09         (~ (v2_pre_topc @ X32)
% 5.83/6.09          | ~ (v8_pre_topc @ X32)
% 5.83/6.09          | ~ (v3_orders_2 @ X32)
% 5.83/6.09          | ~ (v4_orders_2 @ X32)
% 5.83/6.09          | ~ (v5_orders_2 @ X32)
% 5.83/6.09          | ~ (v1_lattice3 @ X32)
% 5.83/6.09          | ~ (v2_lattice3 @ X32)
% 5.83/6.09          | ~ (v1_compts_1 @ X32)
% 5.83/6.09          | ~ (l1_waybel_9 @ X32)
% 5.83/6.09          | (m1_subset_1 @ (sk_E @ X32) @ (u1_struct_0 @ X32))
% 5.83/6.09          | ~ (v11_waybel_0 @ X31 @ X32)
% 5.83/6.09          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 5.83/6.09          | (r1_lattice3 @ X32 @ 
% 5.83/6.09             (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 5.83/6.09              (u1_waybel_0 @ X32 @ X31)) @ 
% 5.83/6.09             X33)
% 5.83/6.09          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 5.83/6.09          | ~ (l1_waybel_0 @ X31 @ X32)
% 5.83/6.09          | ~ (v7_waybel_0 @ X31)
% 5.83/6.09          | ~ (v4_orders_2 @ X31)
% 5.83/6.09          | (v2_struct_0 @ X31))),
% 5.83/6.09      inference('simplify', [status(thm)], ['18'])).
% 5.83/6.09  thf('20', plain,
% 5.83/6.09      (![X0 : $i]:
% 5.83/6.09         ((v2_struct_0 @ X0)
% 5.83/6.09          | ~ (v4_orders_2 @ X0)
% 5.83/6.09          | ~ (v7_waybel_0 @ X0)
% 5.83/6.09          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 5.83/6.09          | (r1_lattice3 @ sk_A @ 
% 5.83/6.09             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 5.83/6.09              (u1_waybel_0 @ sk_A @ X0)) @ 
% 5.83/6.09             sk_B)
% 5.83/6.09          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 5.83/6.09          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 5.83/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.83/6.09          | ~ (l1_waybel_9 @ sk_A)
% 5.83/6.09          | ~ (v1_compts_1 @ sk_A)
% 5.83/6.09          | ~ (v2_lattice3 @ sk_A)
% 5.83/6.09          | ~ (v1_lattice3 @ sk_A)
% 5.83/6.09          | ~ (v5_orders_2 @ sk_A)
% 5.83/6.09          | ~ (v4_orders_2 @ sk_A)
% 5.83/6.09          | ~ (v3_orders_2 @ sk_A)
% 5.83/6.09          | ~ (v8_pre_topc @ sk_A)
% 5.83/6.09          | ~ (v2_pre_topc @ sk_A))),
% 5.83/6.09      inference('sup-', [status(thm)], ['17', '19'])).
% 5.83/6.09  thf('21', plain, ((l1_waybel_9 @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('22', plain, ((v1_compts_1 @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('23', plain, ((v2_lattice3 @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('24', plain, ((v1_lattice3 @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('25', plain, ((v5_orders_2 @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('26', plain, ((v4_orders_2 @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('27', plain, ((v3_orders_2 @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('28', plain, ((v8_pre_topc @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 5.83/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.83/6.09  thf('30', plain,
% 5.83/6.09      (![X0 : $i]:
% 5.83/6.09         ((v2_struct_0 @ X0)
% 5.83/6.09          | ~ (v4_orders_2 @ X0)
% 5.83/6.09          | ~ (v7_waybel_0 @ X0)
% 5.83/6.09          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 5.83/6.09          | (r1_lattice3 @ sk_A @ 
% 5.83/6.09             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 5.83/6.09              (u1_waybel_0 @ sk_A @ X0)) @ 
% 5.83/6.09             sk_B)
% 5.83/6.09          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('demod', [status(thm)],
% 5.92/6.09                ['20', '21', '22', '23', '24', '25', '26', '27', '28', '29'])).
% 5.92/6.09  thf('31', plain,
% 5.92/6.09      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | ~ (v11_waybel_0 @ sk_C @ sk_A)
% 5.92/6.09        | (r1_lattice3 @ sk_A @ 
% 5.92/6.09           (k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.92/6.09            (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           sk_B)
% 5.92/6.09        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 5.92/6.09        | ~ (v7_waybel_0 @ sk_C)
% 5.92/6.09        | ~ (v4_orders_2 @ sk_C)
% 5.92/6.09        | (v2_struct_0 @ sk_C))),
% 5.92/6.09      inference('sup-', [status(thm)], ['16', '30'])).
% 5.92/6.09  thf('32', plain, ((v11_waybel_0 @ sk_C @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('33', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf(dt_u1_waybel_0, axiom,
% 5.92/6.09    (![A:$i,B:$i]:
% 5.92/6.09     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 5.92/6.09       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 5.92/6.09         ( v1_funct_2 @
% 5.92/6.09           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 5.92/6.09         ( m1_subset_1 @
% 5.92/6.09           ( u1_waybel_0 @ A @ B ) @ 
% 5.92/6.09           ( k1_zfmisc_1 @
% 5.92/6.09             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 5.92/6.09  thf('34', plain,
% 5.92/6.09      (![X24 : $i, X25 : $i]:
% 5.92/6.09         (~ (l1_struct_0 @ X24)
% 5.92/6.09          | ~ (l1_waybel_0 @ X25 @ X24)
% 5.92/6.09          | (m1_subset_1 @ (u1_waybel_0 @ X24 @ X25) @ 
% 5.92/6.09             (k1_zfmisc_1 @ 
% 5.92/6.09              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24)))))),
% 5.92/6.09      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 5.92/6.09  thf('35', plain,
% 5.92/6.09      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 5.92/6.09         (k1_zfmisc_1 @ 
% 5.92/6.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 5.92/6.09        | ~ (l1_struct_0 @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['33', '34'])).
% 5.92/6.09  thf('36', plain, ((l1_waybel_9 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('37', plain,
% 5.92/6.09      (![X30 : $i]: ((l1_orders_2 @ X30) | ~ (l1_waybel_9 @ X30))),
% 5.92/6.09      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 5.92/6.09  thf(dt_l1_orders_2, axiom,
% 5.92/6.09    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 5.92/6.09  thf('38', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 5.92/6.09      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 5.92/6.09  thf('39', plain, (![X0 : $i]: (~ (l1_waybel_9 @ X0) | (l1_struct_0 @ X0))),
% 5.92/6.09      inference('sup-', [status(thm)], ['37', '38'])).
% 5.92/6.09  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 5.92/6.09      inference('sup-', [status(thm)], ['36', '39'])).
% 5.92/6.09  thf('41', plain,
% 5.92/6.09      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 5.92/6.09        (k1_zfmisc_1 @ 
% 5.92/6.09         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 5.92/6.09      inference('demod', [status(thm)], ['35', '40'])).
% 5.92/6.09  thf(redefinition_k2_relset_1, axiom,
% 5.92/6.09    (![A:$i,B:$i,C:$i]:
% 5.92/6.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.92/6.09       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.92/6.09  thf('42', plain,
% 5.92/6.09      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.92/6.09         (((k2_relset_1 @ X4 @ X5 @ X3) = (k2_relat_1 @ X3))
% 5.92/6.09          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 5.92/6.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.92/6.09  thf('43', plain,
% 5.92/6.09      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.92/6.09         (u1_waybel_0 @ sk_A @ sk_C))
% 5.92/6.09         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 5.92/6.09      inference('sup-', [status(thm)], ['41', '42'])).
% 5.92/6.09  thf('44', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('45', plain, ((v7_waybel_0 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('46', plain, ((v4_orders_2 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('47', plain,
% 5.92/6.09      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           sk_B)
% 5.92/6.09        | (v2_struct_0 @ sk_C))),
% 5.92/6.09      inference('demod', [status(thm)], ['31', '32', '43', '44', '45', '46'])).
% 5.92/6.09  thf('48', plain, (~ (v2_struct_0 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('49', plain,
% 5.92/6.09      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('clc', [status(thm)], ['47', '48'])).
% 5.92/6.09  thf('50', plain,
% 5.92/6.09      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('clc', [status(thm)], ['47', '48'])).
% 5.92/6.09  thf(t31_yellow_0, axiom,
% 5.92/6.09    (![A:$i]:
% 5.92/6.09     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 5.92/6.09       ( ![B:$i]:
% 5.92/6.09         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.92/6.09           ( ![C:$i]:
% 5.92/6.09             ( ( ( ( r2_yellow_0 @ A @ C ) & 
% 5.92/6.09                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) =>
% 5.92/6.09                 ( ( ![D:$i]:
% 5.92/6.09                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.92/6.09                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 5.92/6.09                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 5.92/6.09                   ( r1_lattice3 @ A @ C @ B ) ) ) & 
% 5.92/6.09               ( ( ( ![D:$i]:
% 5.92/6.09                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.92/6.09                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 5.92/6.09                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 5.92/6.09                   ( r1_lattice3 @ A @ C @ B ) ) =>
% 5.92/6.09                 ( ( r2_yellow_0 @ A @ C ) & 
% 5.92/6.09                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 5.92/6.09  thf(zf_stmt_1, axiom,
% 5.92/6.09    (![D:$i,C:$i,B:$i,A:$i]:
% 5.92/6.09     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.92/6.09         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 5.92/6.09       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 5.92/6.09  thf('51', plain,
% 5.92/6.09      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.92/6.09          | (m1_subset_1 @ X12 @ (u1_struct_0 @ X15)))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.09  thf('52', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf(zf_stmt_2, axiom,
% 5.92/6.09    (![D:$i,C:$i,B:$i,A:$i]:
% 5.92/6.09     ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ D @ B ) ) =>
% 5.92/6.09       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 5.92/6.09  thf('53', plain,
% 5.92/6.09      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.92/6.09         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11) | (r1_lattice3 @ X11 @ X9 @ X8))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.92/6.09  thf('54', plain,
% 5.92/6.09      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('clc', [status(thm)], ['47', '48'])).
% 5.92/6.09  thf('55', plain,
% 5.92/6.09      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('clc', [status(thm)], ['47', '48'])).
% 5.92/6.09  thf('56', plain,
% 5.92/6.09      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.92/6.09          | (m1_subset_1 @ X12 @ (u1_struct_0 @ X15)))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.09  thf('57', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('58', plain,
% 5.92/6.09      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.92/6.09         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11) | (r1_lattice3 @ X11 @ X9 @ X8))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.92/6.09  thf('59', plain,
% 5.92/6.09      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.92/6.09         (u1_waybel_0 @ sk_A @ sk_C))
% 5.92/6.09         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 5.92/6.09      inference('sup-', [status(thm)], ['41', '42'])).
% 5.92/6.09  thf(l52_waybel_9, axiom,
% 5.92/6.09    (![A:$i]:
% 5.92/6.09     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 5.92/6.09         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 5.92/6.09         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 5.92/6.09       ( ![B:$i]:
% 5.92/6.09         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 5.92/6.09             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 5.92/6.09           ( ![C:$i]:
% 5.92/6.09             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.92/6.09               ( ![D:$i]:
% 5.92/6.09                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.92/6.09                   ( ( ( ( C ) = ( D ) ) & 
% 5.92/6.09                       ( ![E:$i]:
% 5.92/6.09                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 5.92/6.09                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 5.92/6.09                       ( r3_waybel_9 @ A @ B @ C ) ) =>
% 5.92/6.09                     ( ![E:$i]:
% 5.92/6.09                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 5.92/6.09                         ( ( r1_lattice3 @
% 5.92/6.09                             A @ 
% 5.92/6.09                             ( k2_relset_1 @
% 5.92/6.09                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 5.92/6.09                               ( u1_waybel_0 @ A @ B ) ) @ 
% 5.92/6.09                             E ) =>
% 5.92/6.09                           ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 5.92/6.09  thf('60', plain,
% 5.92/6.09      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 5.92/6.09         ((v2_struct_0 @ X35)
% 5.92/6.09          | ~ (v4_orders_2 @ X35)
% 5.92/6.09          | ~ (v7_waybel_0 @ X35)
% 5.92/6.09          | ~ (l1_waybel_0 @ X35 @ X36)
% 5.92/6.09          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 5.92/6.09          | ~ (r1_lattice3 @ X36 @ 
% 5.92/6.09               (k2_relset_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36) @ 
% 5.92/6.09                (u1_waybel_0 @ X36 @ X35)) @ 
% 5.92/6.09               X38)
% 5.92/6.09          | (r1_orders_2 @ X36 @ X38 @ X37)
% 5.92/6.09          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 5.92/6.09          | ((X39) != (X37))
% 5.92/6.09          | ~ (r3_waybel_9 @ X36 @ X35 @ X39)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ X36) @ (u1_struct_0 @ X36))
% 5.92/6.09          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 5.92/6.09          | ~ (l1_waybel_9 @ X36)
% 5.92/6.09          | ~ (v1_compts_1 @ X36)
% 5.92/6.09          | ~ (v2_lattice3 @ X36)
% 5.92/6.09          | ~ (v1_lattice3 @ X36)
% 5.92/6.09          | ~ (v5_orders_2 @ X36)
% 5.92/6.09          | ~ (v4_orders_2 @ X36)
% 5.92/6.09          | ~ (v3_orders_2 @ X36)
% 5.92/6.09          | ~ (v8_pre_topc @ X36)
% 5.92/6.09          | ~ (v2_pre_topc @ X36))),
% 5.92/6.09      inference('cnf', [status(esa)], [l52_waybel_9])).
% 5.92/6.09  thf('61', plain,
% 5.92/6.09      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 5.92/6.09         (~ (v2_pre_topc @ X36)
% 5.92/6.09          | ~ (v8_pre_topc @ X36)
% 5.92/6.09          | ~ (v3_orders_2 @ X36)
% 5.92/6.09          | ~ (v4_orders_2 @ X36)
% 5.92/6.09          | ~ (v5_orders_2 @ X36)
% 5.92/6.09          | ~ (v1_lattice3 @ X36)
% 5.92/6.09          | ~ (v2_lattice3 @ X36)
% 5.92/6.09          | ~ (v1_compts_1 @ X36)
% 5.92/6.09          | ~ (l1_waybel_9 @ X36)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ X36) @ (u1_struct_0 @ X36))
% 5.92/6.09          | ~ (r3_waybel_9 @ X36 @ X35 @ X37)
% 5.92/6.09          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 5.92/6.09          | (r1_orders_2 @ X36 @ X38 @ X37)
% 5.92/6.09          | ~ (r1_lattice3 @ X36 @ 
% 5.92/6.09               (k2_relset_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36) @ 
% 5.92/6.09                (u1_waybel_0 @ X36 @ X35)) @ 
% 5.92/6.09               X38)
% 5.92/6.09          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 5.92/6.09          | ~ (l1_waybel_0 @ X35 @ X36)
% 5.92/6.09          | ~ (v7_waybel_0 @ X35)
% 5.92/6.09          | ~ (v4_orders_2 @ X35)
% 5.92/6.09          | (v2_struct_0 @ X35))),
% 5.92/6.09      inference('simplify', [status(thm)], ['60'])).
% 5.92/6.09  thf('62', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X0)
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | ~ (v4_orders_2 @ sk_C)
% 5.92/6.09          | ~ (v7_waybel_0 @ sk_C)
% 5.92/6.09          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 5.92/6.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | ~ (l1_waybel_9 @ sk_A)
% 5.92/6.09          | ~ (v1_compts_1 @ sk_A)
% 5.92/6.09          | ~ (v2_lattice3 @ sk_A)
% 5.92/6.09          | ~ (v1_lattice3 @ sk_A)
% 5.92/6.09          | ~ (v5_orders_2 @ sk_A)
% 5.92/6.09          | ~ (v4_orders_2 @ sk_A)
% 5.92/6.09          | ~ (v3_orders_2 @ sk_A)
% 5.92/6.09          | ~ (v8_pre_topc @ sk_A)
% 5.92/6.09          | ~ (v2_pre_topc @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['59', '61'])).
% 5.92/6.09  thf('63', plain, ((v4_orders_2 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('64', plain, ((v7_waybel_0 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('65', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('66', plain, ((l1_waybel_9 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('67', plain, ((v1_compts_1 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('68', plain, ((v2_lattice3 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('69', plain, ((v1_lattice3 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('70', plain, ((v5_orders_2 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('71', plain, ((v4_orders_2 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('72', plain, ((v3_orders_2 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('73', plain, ((v8_pre_topc @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('75', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X0)
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('demod', [status(thm)],
% 5.92/6.09                ['62', '63', '64', '65', '66', '67', '68', '69', '70', '71', 
% 5.92/6.09                 '72', '73', '74'])).
% 5.92/6.09  thf('76', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.92/6.09         ((zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           X2 @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.92/6.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (v2_struct_0 @ sk_C))),
% 5.92/6.09      inference('sup-', [status(thm)], ['58', '75'])).
% 5.92/6.09  thf('77', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         ((v2_struct_0 @ sk_C)
% 5.92/6.09          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X1 @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['57', '76'])).
% 5.92/6.09  thf('78', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('79', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         ((v2_struct_0 @ sk_C)
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X1 @ sk_A))),
% 5.92/6.09      inference('demod', [status(thm)], ['77', '78'])).
% 5.92/6.09  thf('80', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 5.92/6.09          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X1 @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | (v2_struct_0 @ sk_C))),
% 5.92/6.09      inference('sup-', [status(thm)], ['56', '79'])).
% 5.92/6.09  thf('81', plain,
% 5.92/6.09      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.92/6.09          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.09  thf('82', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.92/6.09         ((v2_struct_0 @ sk_C)
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A)
% 5.92/6.09          | (zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X0 @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['80', '81'])).
% 5.92/6.09  thf('83', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           X0 @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 5.92/6.09          | (v2_struct_0 @ sk_C))),
% 5.92/6.09      inference('eq_fact', [status(thm)], ['82'])).
% 5.92/6.09  thf('84', plain,
% 5.92/6.09      (![X30 : $i]: ((l1_orders_2 @ X30) | ~ (l1_waybel_9 @ X30))),
% 5.92/6.09      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 5.92/6.09  thf('85', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 5.92/6.09  thf(zf_stmt_4, axiom,
% 5.92/6.09    (![C:$i,B:$i,A:$i]:
% 5.92/6.09     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 5.92/6.09       ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & ( r2_yellow_0 @ A @ C ) ) ))).
% 5.92/6.09  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 5.92/6.09  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 5.92/6.09  thf(zf_stmt_7, axiom,
% 5.92/6.09    (![A:$i]:
% 5.92/6.09     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.92/6.09       ( ![B:$i]:
% 5.92/6.09         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.92/6.09           ( ![C:$i]:
% 5.92/6.09             ( ( ( ( r1_lattice3 @ A @ C @ B ) & 
% 5.92/6.09                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 5.92/6.09                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 5.92/6.09               ( ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & 
% 5.92/6.09                   ( r2_yellow_0 @ A @ C ) ) =>
% 5.92/6.09                 ( ( r1_lattice3 @ A @ C @ B ) & 
% 5.92/6.09                   ( ![D:$i]:
% 5.92/6.09                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.92/6.09                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 5.92/6.09                         ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 5.92/6.09  thf('86', plain,
% 5.92/6.09      (![X19 : $i, X20 : $i, X23 : $i]:
% 5.92/6.09         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 5.92/6.09          | ~ (r1_lattice3 @ X20 @ X23 @ X19)
% 5.92/6.09          | ~ (zip_tseitin_1 @ (sk_D @ X23 @ X19 @ X20) @ X23 @ X19 @ X20)
% 5.92/6.09          | (zip_tseitin_2 @ X23 @ X19 @ X20)
% 5.92/6.09          | ~ (l1_orders_2 @ X20)
% 5.92/6.09          | ~ (v5_orders_2 @ X20))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_7])).
% 5.92/6.09  thf('87', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (~ (v5_orders_2 @ sk_A)
% 5.92/6.09          | ~ (l1_orders_2 @ sk_A)
% 5.92/6.09          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.92/6.09      inference('sup-', [status(thm)], ['85', '86'])).
% 5.92/6.09  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('89', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (~ (l1_orders_2 @ sk_A)
% 5.92/6.09          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.92/6.09      inference('demod', [status(thm)], ['87', '88'])).
% 5.92/6.09  thf('90', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (~ (l1_waybel_9 @ sk_A)
% 5.92/6.09          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['84', '89'])).
% 5.92/6.09  thf('91', plain, ((l1_waybel_9 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('92', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('demod', [status(thm)], ['90', '91'])).
% 5.92/6.09  thf('93', plain,
% 5.92/6.09      (((v2_struct_0 @ sk_C)
% 5.92/6.09        | (r1_orders_2 @ sk_A @ 
% 5.92/6.09           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09           sk_B)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B))),
% 5.92/6.09      inference('sup-', [status(thm)], ['83', '92'])).
% 5.92/6.09  thf('94', plain,
% 5.92/6.09      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (r1_orders_2 @ sk_A @ 
% 5.92/6.09           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09           sk_B)
% 5.92/6.09        | (v2_struct_0 @ sk_C))),
% 5.92/6.09      inference('sup-', [status(thm)], ['55', '93'])).
% 5.92/6.09  thf('95', plain,
% 5.92/6.09      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.92/6.09         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 5.92/6.09          | ~ (r1_orders_2 @ X11 @ X8 @ X10))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.92/6.09  thf('96', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         ((v2_struct_0 @ sk_C)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_0 @ 
% 5.92/6.09             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09             X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['94', '95'])).
% 5.92/6.09  thf('97', plain,
% 5.92/6.09      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.92/6.09          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.09  thf('98', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         ((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | (zip_tseitin_1 @ 
% 5.92/6.09             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09             X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['96', '97'])).
% 5.92/6.09  thf('99', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('demod', [status(thm)], ['90', '91'])).
% 5.92/6.09  thf('100', plain,
% 5.92/6.09      (((v2_struct_0 @ sk_C)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B))),
% 5.92/6.09      inference('sup-', [status(thm)], ['98', '99'])).
% 5.92/6.09  thf('101', plain,
% 5.92/6.09      ((~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           sk_B)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (v2_struct_0 @ sk_C))),
% 5.92/6.09      inference('simplify', [status(thm)], ['100'])).
% 5.92/6.09  thf('102', plain,
% 5.92/6.09      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('sup-', [status(thm)], ['54', '101'])).
% 5.92/6.09  thf('103', plain,
% 5.92/6.09      (((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09         sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('simplify', [status(thm)], ['102'])).
% 5.92/6.09  thf('104', plain,
% 5.92/6.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.92/6.09         (((X18) = (k2_yellow_0 @ X16 @ X17))
% 5.92/6.09          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.92/6.09  thf('105', plain,
% 5.92/6.09      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('sup-', [status(thm)], ['103', '104'])).
% 5.92/6.09  thf('106', plain,
% 5.92/6.09      (![X40 : $i]:
% 5.92/6.09         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 5.92/6.09          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('107', plain,
% 5.92/6.09      ((((sk_B)
% 5.92/6.09          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['105', '106'])).
% 5.92/6.09  thf('108', plain,
% 5.92/6.09      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.92/6.09         (u1_waybel_0 @ sk_A @ sk_C))
% 5.92/6.09         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 5.92/6.09      inference('sup-', [status(thm)], ['41', '42'])).
% 5.92/6.09  thf('109', plain,
% 5.92/6.09      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 5.92/6.09         ((v2_struct_0 @ X35)
% 5.92/6.09          | ~ (v4_orders_2 @ X35)
% 5.92/6.09          | ~ (v7_waybel_0 @ X35)
% 5.92/6.09          | ~ (l1_waybel_0 @ X35 @ X36)
% 5.92/6.09          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 5.92/6.09          | ~ (r1_lattice3 @ X36 @ 
% 5.92/6.09               (k2_relset_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36) @ 
% 5.92/6.09                (u1_waybel_0 @ X36 @ X35)) @ 
% 5.92/6.09               X38)
% 5.92/6.09          | (r1_orders_2 @ X36 @ X38 @ X37)
% 5.92/6.09          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 5.92/6.09          | ((X39) != (X37))
% 5.92/6.09          | ~ (r3_waybel_9 @ X36 @ X35 @ X39)
% 5.92/6.09          | ~ (v5_pre_topc @ (k4_waybel_1 @ X36 @ (sk_E_1 @ X36)) @ X36 @ X36)
% 5.92/6.09          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 5.92/6.09          | ~ (l1_waybel_9 @ X36)
% 5.92/6.09          | ~ (v1_compts_1 @ X36)
% 5.92/6.09          | ~ (v2_lattice3 @ X36)
% 5.92/6.09          | ~ (v1_lattice3 @ X36)
% 5.92/6.09          | ~ (v5_orders_2 @ X36)
% 5.92/6.09          | ~ (v4_orders_2 @ X36)
% 5.92/6.09          | ~ (v3_orders_2 @ X36)
% 5.92/6.09          | ~ (v8_pre_topc @ X36)
% 5.92/6.09          | ~ (v2_pre_topc @ X36))),
% 5.92/6.09      inference('cnf', [status(esa)], [l52_waybel_9])).
% 5.92/6.09  thf('110', plain,
% 5.92/6.09      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 5.92/6.09         (~ (v2_pre_topc @ X36)
% 5.92/6.09          | ~ (v8_pre_topc @ X36)
% 5.92/6.09          | ~ (v3_orders_2 @ X36)
% 5.92/6.09          | ~ (v4_orders_2 @ X36)
% 5.92/6.09          | ~ (v5_orders_2 @ X36)
% 5.92/6.09          | ~ (v1_lattice3 @ X36)
% 5.92/6.09          | ~ (v2_lattice3 @ X36)
% 5.92/6.09          | ~ (v1_compts_1 @ X36)
% 5.92/6.09          | ~ (l1_waybel_9 @ X36)
% 5.92/6.09          | ~ (v5_pre_topc @ (k4_waybel_1 @ X36 @ (sk_E_1 @ X36)) @ X36 @ X36)
% 5.92/6.09          | ~ (r3_waybel_9 @ X36 @ X35 @ X37)
% 5.92/6.09          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 5.92/6.09          | (r1_orders_2 @ X36 @ X38 @ X37)
% 5.92/6.09          | ~ (r1_lattice3 @ X36 @ 
% 5.92/6.09               (k2_relset_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36) @ 
% 5.92/6.09                (u1_waybel_0 @ X36 @ X35)) @ 
% 5.92/6.09               X38)
% 5.92/6.09          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 5.92/6.09          | ~ (l1_waybel_0 @ X35 @ X36)
% 5.92/6.09          | ~ (v7_waybel_0 @ X35)
% 5.92/6.09          | ~ (v4_orders_2 @ X35)
% 5.92/6.09          | (v2_struct_0 @ X35))),
% 5.92/6.09      inference('simplify', [status(thm)], ['109'])).
% 5.92/6.09  thf('111', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X0)
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | ~ (v4_orders_2 @ sk_C)
% 5.92/6.09          | ~ (v7_waybel_0 @ sk_C)
% 5.92/6.09          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 5.92/6.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.92/6.09          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 5.92/6.09               sk_A)
% 5.92/6.09          | ~ (l1_waybel_9 @ sk_A)
% 5.92/6.09          | ~ (v1_compts_1 @ sk_A)
% 5.92/6.09          | ~ (v2_lattice3 @ sk_A)
% 5.92/6.09          | ~ (v1_lattice3 @ sk_A)
% 5.92/6.09          | ~ (v5_orders_2 @ sk_A)
% 5.92/6.09          | ~ (v4_orders_2 @ sk_A)
% 5.92/6.09          | ~ (v3_orders_2 @ sk_A)
% 5.92/6.09          | ~ (v8_pre_topc @ sk_A)
% 5.92/6.09          | ~ (v2_pre_topc @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['108', '110'])).
% 5.92/6.09  thf('112', plain, ((v4_orders_2 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('113', plain, ((v7_waybel_0 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('114', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('115', plain, ((l1_waybel_9 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('116', plain, ((v1_compts_1 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('117', plain, ((v2_lattice3 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('118', plain, ((v1_lattice3 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('119', plain, ((v5_orders_2 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('120', plain, ((v4_orders_2 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('121', plain, ((v3_orders_2 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('122', plain, ((v8_pre_topc @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('124', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X0)
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.92/6.09          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 5.92/6.09               sk_A))),
% 5.92/6.09      inference('demod', [status(thm)],
% 5.92/6.09                ['111', '112', '113', '114', '115', '116', '117', '118', 
% 5.92/6.09                 '119', '120', '121', '122', '123'])).
% 5.92/6.09  thf('125', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         ((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 5.92/6.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X1 @ X0)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | ~ (r1_lattice3 @ sk_A @ 
% 5.92/6.09               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X1))),
% 5.92/6.09      inference('sup-', [status(thm)], ['107', '124'])).
% 5.92/6.09  thf('126', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X1)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X1 @ X0)
% 5.92/6.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('simplify', [status(thm)], ['125'])).
% 5.92/6.09  thf('127', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.92/6.09         ((zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           X2 @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.92/6.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('sup-', [status(thm)], ['53', '126'])).
% 5.92/6.09  thf('128', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X1 @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['52', '127'])).
% 5.92/6.09  thf('129', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('130', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         ((r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X1 @ sk_A))),
% 5.92/6.09      inference('demod', [status(thm)], ['128', '129'])).
% 5.92/6.09  thf('131', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 5.92/6.09          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X1 @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 5.92/6.09      inference('sup-', [status(thm)], ['51', '130'])).
% 5.92/6.09  thf('132', plain,
% 5.92/6.09      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.92/6.09          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.09  thf('133', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.92/6.09         ((r1_orders_2 @ sk_A @ X1 @ sk_B)
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A)
% 5.92/6.09          | (zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             X0 @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['131', '132'])).
% 5.92/6.09  thf('134', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           X0 @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (r1_orders_2 @ sk_A @ X1 @ sk_B))),
% 5.92/6.09      inference('eq_fact', [status(thm)], ['133'])).
% 5.92/6.09  thf('135', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('demod', [status(thm)], ['90', '91'])).
% 5.92/6.09  thf('136', plain,
% 5.92/6.09      (((r1_orders_2 @ sk_A @ 
% 5.92/6.09         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09         sk_B)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B))),
% 5.92/6.09      inference('sup-', [status(thm)], ['134', '135'])).
% 5.92/6.09  thf('137', plain,
% 5.92/6.09      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (r1_orders_2 @ sk_A @ 
% 5.92/6.09           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09           sk_B))),
% 5.92/6.09      inference('sup-', [status(thm)], ['50', '136'])).
% 5.92/6.09  thf('138', plain,
% 5.92/6.09      (((r1_orders_2 @ sk_A @ 
% 5.92/6.09         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09         sk_B)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('simplify', [status(thm)], ['137'])).
% 5.92/6.09  thf('139', plain,
% 5.92/6.09      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.92/6.09         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 5.92/6.09          | ~ (r1_orders_2 @ X11 @ X8 @ X10))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.92/6.09  thf('140', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         ((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B @ sk_A)
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (zip_tseitin_0 @ 
% 5.92/6.09             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09             X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['138', '139'])).
% 5.92/6.09  thf('141', plain,
% 5.92/6.09      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.92/6.09          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.09  thf('142', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_1 @ 
% 5.92/6.09             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09             X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['140', '141'])).
% 5.92/6.09  thf('143', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('demod', [status(thm)], ['90', '91'])).
% 5.92/6.09  thf('144', plain,
% 5.92/6.09      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B))),
% 5.92/6.09      inference('sup-', [status(thm)], ['142', '143'])).
% 5.92/6.09  thf('145', plain,
% 5.92/6.09      ((~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           sk_B)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('simplify', [status(thm)], ['144'])).
% 5.92/6.09  thf('146', plain,
% 5.92/6.09      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('sup-', [status(thm)], ['49', '145'])).
% 5.92/6.09  thf('147', plain,
% 5.92/6.09      ((((sk_B)
% 5.92/6.09          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('simplify', [status(thm)], ['146'])).
% 5.92/6.09  thf('148', plain,
% 5.92/6.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.92/6.09         (((X18) = (k2_yellow_0 @ X16 @ X17))
% 5.92/6.09          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.92/6.09  thf('149', plain,
% 5.92/6.09      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('sup-', [status(thm)], ['147', '148'])).
% 5.92/6.09  thf('150', plain,
% 5.92/6.09      ((((sk_B)
% 5.92/6.09          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('simplify', [status(thm)], ['149'])).
% 5.92/6.09  thf('151', plain, (~ (v2_struct_0 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('152', plain,
% 5.92/6.09      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('clc', [status(thm)], ['150', '151'])).
% 5.92/6.09  thf('153', plain,
% 5.92/6.09      (![X40 : $i]:
% 5.92/6.09         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 5.92/6.09          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('154', plain,
% 5.92/6.09      ((((sk_B)
% 5.92/6.09          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E @ sk_A)) @ sk_A @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['152', '153'])).
% 5.92/6.09  thf('155', plain,
% 5.92/6.09      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 5.92/6.09         ((v2_struct_0 @ X31)
% 5.92/6.09          | ~ (v4_orders_2 @ X31)
% 5.92/6.09          | ~ (v7_waybel_0 @ X31)
% 5.92/6.09          | ~ (l1_waybel_0 @ X31 @ X32)
% 5.92/6.09          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 5.92/6.09          | (r1_lattice3 @ X32 @ 
% 5.92/6.09             (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 5.92/6.09              (u1_waybel_0 @ X32 @ X31)) @ 
% 5.92/6.09             X33)
% 5.92/6.09          | ((X34) != (X33))
% 5.92/6.09          | ~ (r3_waybel_9 @ X32 @ X31 @ X34)
% 5.92/6.09          | ~ (v11_waybel_0 @ X31 @ X32)
% 5.92/6.09          | ~ (v5_pre_topc @ (k4_waybel_1 @ X32 @ (sk_E @ X32)) @ X32 @ X32)
% 5.92/6.09          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 5.92/6.09          | ~ (l1_waybel_9 @ X32)
% 5.92/6.09          | ~ (v1_compts_1 @ X32)
% 5.92/6.09          | ~ (v2_lattice3 @ X32)
% 5.92/6.09          | ~ (v1_lattice3 @ X32)
% 5.92/6.09          | ~ (v5_orders_2 @ X32)
% 5.92/6.09          | ~ (v4_orders_2 @ X32)
% 5.92/6.09          | ~ (v3_orders_2 @ X32)
% 5.92/6.09          | ~ (v8_pre_topc @ X32)
% 5.92/6.09          | ~ (v2_pre_topc @ X32))),
% 5.92/6.09      inference('cnf', [status(esa)], [l51_waybel_9])).
% 5.92/6.09  thf('156', plain,
% 5.92/6.09      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.92/6.09         (~ (v2_pre_topc @ X32)
% 5.92/6.09          | ~ (v8_pre_topc @ X32)
% 5.92/6.09          | ~ (v3_orders_2 @ X32)
% 5.92/6.09          | ~ (v4_orders_2 @ X32)
% 5.92/6.09          | ~ (v5_orders_2 @ X32)
% 5.92/6.09          | ~ (v1_lattice3 @ X32)
% 5.92/6.09          | ~ (v2_lattice3 @ X32)
% 5.92/6.09          | ~ (v1_compts_1 @ X32)
% 5.92/6.09          | ~ (l1_waybel_9 @ X32)
% 5.92/6.09          | ~ (v5_pre_topc @ (k4_waybel_1 @ X32 @ (sk_E @ X32)) @ X32 @ X32)
% 5.92/6.09          | ~ (v11_waybel_0 @ X31 @ X32)
% 5.92/6.09          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 5.92/6.09          | (r1_lattice3 @ X32 @ 
% 5.92/6.09             (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 5.92/6.09              (u1_waybel_0 @ X32 @ X31)) @ 
% 5.92/6.09             X33)
% 5.92/6.09          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 5.92/6.09          | ~ (l1_waybel_0 @ X31 @ X32)
% 5.92/6.09          | ~ (v7_waybel_0 @ X31)
% 5.92/6.09          | ~ (v4_orders_2 @ X31)
% 5.92/6.09          | (v2_struct_0 @ X31))),
% 5.92/6.09      inference('simplify', [status(thm)], ['155'])).
% 5.92/6.09  thf('157', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         (((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (v2_struct_0 @ X0)
% 5.92/6.09          | ~ (v4_orders_2 @ X0)
% 5.92/6.09          | ~ (v7_waybel_0 @ X0)
% 5.92/6.09          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 5.92/6.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_lattice3 @ sk_A @ 
% 5.92/6.09             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 5.92/6.09              (u1_waybel_0 @ sk_A @ X0)) @ 
% 5.92/6.09             X1)
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 5.92/6.09          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 5.92/6.09          | ~ (l1_waybel_9 @ sk_A)
% 5.92/6.09          | ~ (v1_compts_1 @ sk_A)
% 5.92/6.09          | ~ (v2_lattice3 @ sk_A)
% 5.92/6.09          | ~ (v1_lattice3 @ sk_A)
% 5.92/6.09          | ~ (v5_orders_2 @ sk_A)
% 5.92/6.09          | ~ (v4_orders_2 @ sk_A)
% 5.92/6.09          | ~ (v3_orders_2 @ sk_A)
% 5.92/6.09          | ~ (v8_pre_topc @ sk_A)
% 5.92/6.09          | ~ (v2_pre_topc @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['154', '156'])).
% 5.92/6.09  thf('158', plain, ((l1_waybel_9 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('159', plain, ((v1_compts_1 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('160', plain, ((v2_lattice3 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('161', plain, ((v1_lattice3 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('162', plain, ((v5_orders_2 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('163', plain, ((v4_orders_2 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('164', plain, ((v3_orders_2 @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('165', plain, ((v8_pre_topc @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('166', plain, ((v2_pre_topc @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('167', plain,
% 5.92/6.09      (![X0 : $i, X1 : $i]:
% 5.92/6.09         (((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (v2_struct_0 @ X0)
% 5.92/6.09          | ~ (v4_orders_2 @ X0)
% 5.92/6.09          | ~ (v7_waybel_0 @ X0)
% 5.92/6.09          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 5.92/6.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (r1_lattice3 @ sk_A @ 
% 5.92/6.09             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 5.92/6.09              (u1_waybel_0 @ sk_A @ X0)) @ 
% 5.92/6.09             X1)
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 5.92/6.09          | ~ (v11_waybel_0 @ X0 @ sk_A))),
% 5.92/6.09      inference('demod', [status(thm)],
% 5.92/6.09                ['157', '158', '159', '160', '161', '162', '163', '164', 
% 5.92/6.09                 '165', '166'])).
% 5.92/6.09  thf('168', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (~ (v11_waybel_0 @ X0 @ sk_A)
% 5.92/6.09          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | (r1_lattice3 @ sk_A @ 
% 5.92/6.09             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 5.92/6.09              (u1_waybel_0 @ sk_A @ X0)) @ 
% 5.92/6.09             sk_B)
% 5.92/6.09          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 5.92/6.09          | ~ (v7_waybel_0 @ X0)
% 5.92/6.09          | ~ (v4_orders_2 @ X0)
% 5.92/6.09          | (v2_struct_0 @ X0)
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('sup-', [status(thm)], ['15', '167'])).
% 5.92/6.09  thf('169', plain,
% 5.92/6.09      ((((sk_B)
% 5.92/6.09          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | ~ (v4_orders_2 @ sk_C)
% 5.92/6.09        | ~ (v7_waybel_0 @ sk_C)
% 5.92/6.09        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 5.92/6.09        | (r1_lattice3 @ sk_A @ 
% 5.92/6.09           (k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.92/6.09            (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           sk_B)
% 5.92/6.09        | ~ (v11_waybel_0 @ sk_C @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['14', '168'])).
% 5.92/6.09  thf('170', plain, ((v4_orders_2 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('171', plain, ((v7_waybel_0 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('172', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('173', plain,
% 5.92/6.09      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.92/6.09         (u1_waybel_0 @ sk_A @ sk_C))
% 5.92/6.09         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 5.92/6.09      inference('sup-', [status(thm)], ['41', '42'])).
% 5.92/6.09  thf('174', plain, ((v11_waybel_0 @ sk_C @ sk_A)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('175', plain,
% 5.92/6.09      ((((sk_B)
% 5.92/6.09          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           sk_B))),
% 5.92/6.09      inference('demod', [status(thm)],
% 5.92/6.09                ['169', '170', '171', '172', '173', '174'])).
% 5.92/6.09  thf('176', plain, (~ (v2_struct_0 @ sk_C)),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('177', plain,
% 5.92/6.09      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('clc', [status(thm)], ['175', '176'])).
% 5.92/6.09  thf('178', plain,
% 5.92/6.09      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('clc', [status(thm)], ['175', '176'])).
% 5.92/6.09  thf('179', plain,
% 5.92/6.09      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('clc', [status(thm)], ['175', '176'])).
% 5.92/6.09  thf('180', plain,
% 5.92/6.09      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.92/6.09          | (m1_subset_1 @ X12 @ (u1_struct_0 @ X15)))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.09  thf('181', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('demod', [status(thm)], ['90', '91'])).
% 5.92/6.09  thf('182', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.92/6.09      inference('sup-', [status(thm)], ['180', '181'])).
% 5.92/6.09  thf('183', plain,
% 5.92/6.09      ((((sk_B)
% 5.92/6.09          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ 
% 5.92/6.09           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09           (u1_struct_0 @ sk_A)))),
% 5.92/6.09      inference('sup-', [status(thm)], ['179', '182'])).
% 5.92/6.09  thf('184', plain,
% 5.92/6.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.92/6.09         (((X18) = (k2_yellow_0 @ X16 @ X17))
% 5.92/6.09          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.92/6.09  thf('185', plain,
% 5.92/6.09      (((m1_subset_1 @ 
% 5.92/6.09         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09         (u1_struct_0 @ sk_A))
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('clc', [status(thm)], ['183', '184'])).
% 5.92/6.09  thf('186', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.09  thf('187', plain,
% 5.92/6.09      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.92/6.09         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11) | (r1_lattice3 @ X11 @ X9 @ X8))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.92/6.09  thf('188', plain,
% 5.92/6.09      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('clc', [status(thm)], ['175', '176'])).
% 5.92/6.09  thf('189', plain,
% 5.92/6.09      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('clc', [status(thm)], ['175', '176'])).
% 5.92/6.09  thf('190', plain,
% 5.92/6.09      (((v2_struct_0 @ sk_C)
% 5.92/6.09        | (r1_orders_2 @ sk_A @ 
% 5.92/6.09           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09           sk_B)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B))),
% 5.92/6.09      inference('sup-', [status(thm)], ['83', '92'])).
% 5.92/6.09  thf('191', plain,
% 5.92/6.09      ((((sk_B)
% 5.92/6.09          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (r1_orders_2 @ sk_A @ 
% 5.92/6.09           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09           sk_B)
% 5.92/6.09        | (v2_struct_0 @ sk_C))),
% 5.92/6.09      inference('sup-', [status(thm)], ['189', '190'])).
% 5.92/6.09  thf('192', plain,
% 5.92/6.09      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.92/6.09         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 5.92/6.09          | ~ (r1_orders_2 @ X11 @ X8 @ X10))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.92/6.09  thf('193', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         ((v2_struct_0 @ sk_C)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B @ sk_A)
% 5.92/6.09          | ((sk_B)
% 5.92/6.09              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.09                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (zip_tseitin_0 @ 
% 5.92/6.09             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09             X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['191', '192'])).
% 5.92/6.09  thf('194', plain,
% 5.92/6.09      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.92/6.09         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.92/6.09          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.92/6.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.09  thf('195', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B @ sk_A)
% 5.92/6.09          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09          | (v2_struct_0 @ sk_C)
% 5.92/6.09          | (zip_tseitin_1 @ 
% 5.92/6.09             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.09             X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('sup-', [status(thm)], ['193', '194'])).
% 5.92/6.09  thf('196', plain,
% 5.92/6.09      (![X0 : $i]:
% 5.92/6.09         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 5.92/6.09          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.09          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 5.92/6.09      inference('demod', [status(thm)], ['90', '91'])).
% 5.92/6.09  thf('197', plain,
% 5.92/6.09      (((v2_struct_0 @ sk_C)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09             sk_B))),
% 5.92/6.09      inference('sup-', [status(thm)], ['195', '196'])).
% 5.92/6.09  thf('198', plain,
% 5.92/6.09      ((~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.09           sk_B)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (v2_struct_0 @ sk_C))),
% 5.92/6.09      inference('simplify', [status(thm)], ['197'])).
% 5.92/6.09  thf('199', plain,
% 5.92/6.09      ((((sk_B)
% 5.92/6.09          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09           sk_A)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('sup-', [status(thm)], ['188', '198'])).
% 5.92/6.09  thf('200', plain,
% 5.92/6.09      (((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.09         sk_A)
% 5.92/6.09        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.09        | (v2_struct_0 @ sk_C)
% 5.92/6.09        | ((sk_B)
% 5.92/6.09            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.09      inference('simplify', [status(thm)], ['199'])).
% 5.92/6.09  thf('201', plain,
% 5.92/6.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.92/6.09         (((X18) = (k2_yellow_0 @ X16 @ X17))
% 5.92/6.09          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.92/6.10  thf('202', plain,
% 5.92/6.10      ((((sk_B)
% 5.92/6.10          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10        | (v2_struct_0 @ sk_C)
% 5.92/6.10        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.10        | ((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.10      inference('sup-', [status(thm)], ['200', '201'])).
% 5.92/6.10  thf('203', plain,
% 5.92/6.10      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.92/6.10        | (v2_struct_0 @ sk_C)
% 5.92/6.10        | ((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.10      inference('simplify', [status(thm)], ['202'])).
% 5.92/6.10  thf('204', plain, (~ (v2_struct_0 @ sk_C)),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.10  thf('205', plain,
% 5.92/6.10      ((((sk_B)
% 5.92/6.10          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.92/6.10      inference('clc', [status(thm)], ['203', '204'])).
% 5.92/6.10  thf('206', plain,
% 5.92/6.10      (![X40 : $i]:
% 5.92/6.10         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 5.92/6.10          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.10  thf('207', plain,
% 5.92/6.10      ((((sk_B)
% 5.92/6.10          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 5.92/6.10      inference('sup-', [status(thm)], ['205', '206'])).
% 5.92/6.10  thf('208', plain,
% 5.92/6.10      (![X0 : $i, X1 : $i]:
% 5.92/6.10         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.10             X0)
% 5.92/6.10          | (v2_struct_0 @ sk_C)
% 5.92/6.10          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.10          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.92/6.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.10          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.92/6.10          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 5.92/6.10               sk_A))),
% 5.92/6.10      inference('demod', [status(thm)],
% 5.92/6.10                ['111', '112', '113', '114', '115', '116', '117', '118', 
% 5.92/6.10                 '119', '120', '121', '122', '123'])).
% 5.92/6.10  thf('209', plain,
% 5.92/6.10      (![X0 : $i, X1 : $i]:
% 5.92/6.10         (((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 5.92/6.10          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.10          | (r1_orders_2 @ sk_A @ X1 @ X0)
% 5.92/6.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.10          | (v2_struct_0 @ sk_C)
% 5.92/6.10          | ~ (r1_lattice3 @ sk_A @ 
% 5.92/6.10               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X1))),
% 5.92/6.10      inference('sup-', [status(thm)], ['207', '208'])).
% 5.92/6.10  thf('210', plain,
% 5.92/6.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.92/6.10         ((zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.10           X2 @ sk_A)
% 5.92/6.10          | (v2_struct_0 @ sk_C)
% 5.92/6.10          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.92/6.10          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.92/6.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.10          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.92/6.10          | ((sk_B)
% 5.92/6.10              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.10                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.10      inference('sup-', [status(thm)], ['187', '209'])).
% 5.92/6.10  thf('211', plain,
% 5.92/6.10      (![X0 : $i, X1 : $i]:
% 5.92/6.10         (((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10          | ~ (r3_waybel_9 @ sk_A @ sk_C @ sk_B)
% 5.92/6.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.10          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.92/6.10          | (v2_struct_0 @ sk_C)
% 5.92/6.10          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.10             X1 @ sk_A))),
% 5.92/6.10      inference('sup-', [status(thm)], ['186', '210'])).
% 5.92/6.10  thf('212', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.10  thf('213', plain,
% 5.92/6.10      (![X0 : $i, X1 : $i]:
% 5.92/6.10         (((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.92/6.10          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.92/6.10          | (v2_struct_0 @ sk_C)
% 5.92/6.10          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.10             X1 @ sk_A))),
% 5.92/6.10      inference('demod', [status(thm)], ['211', '212'])).
% 5.92/6.10  thf('214', plain,
% 5.92/6.10      (![X0 : $i]:
% 5.92/6.10         (((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10          | (zip_tseitin_0 @ 
% 5.92/6.10             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X0 @ sk_A)
% 5.92/6.10          | (v2_struct_0 @ sk_C)
% 5.92/6.10          | (r1_orders_2 @ sk_A @ 
% 5.92/6.10             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10             sk_B)
% 5.92/6.10          | ((sk_B)
% 5.92/6.10              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.10                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.10      inference('sup-', [status(thm)], ['185', '213'])).
% 5.92/6.10  thf('215', plain,
% 5.92/6.10      (![X0 : $i]:
% 5.92/6.10         ((r1_orders_2 @ sk_A @ 
% 5.92/6.10           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10           sk_B)
% 5.92/6.10          | (v2_struct_0 @ sk_C)
% 5.92/6.10          | (zip_tseitin_0 @ 
% 5.92/6.10             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X0 @ sk_A)
% 5.92/6.10          | ((sk_B)
% 5.92/6.10              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.10                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.10      inference('simplify', [status(thm)], ['214'])).
% 5.92/6.10  thf('216', plain,
% 5.92/6.10      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.92/6.10         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.92/6.10          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.10  thf('217', plain,
% 5.92/6.10      (![X0 : $i]:
% 5.92/6.10         (((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10          | (v2_struct_0 @ sk_C)
% 5.92/6.10          | (r1_orders_2 @ sk_A @ 
% 5.92/6.10             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10             sk_B)
% 5.92/6.10          | (zip_tseitin_1 @ 
% 5.92/6.10             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X0 @ sk_A))),
% 5.92/6.10      inference('sup-', [status(thm)], ['215', '216'])).
% 5.92/6.10  thf('218', plain,
% 5.92/6.10      (![X0 : $i]:
% 5.92/6.10         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 5.92/6.10          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.10          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 5.92/6.10      inference('demod', [status(thm)], ['90', '91'])).
% 5.92/6.10  thf('219', plain,
% 5.92/6.10      (((r1_orders_2 @ sk_A @ 
% 5.92/6.10         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10         sk_B)
% 5.92/6.10        | (v2_struct_0 @ sk_C)
% 5.92/6.10        | ((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.10           sk_A)
% 5.92/6.10        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.10             sk_B))),
% 5.92/6.10      inference('sup-', [status(thm)], ['217', '218'])).
% 5.92/6.10  thf('220', plain,
% 5.92/6.10      ((((sk_B)
% 5.92/6.10          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.10           sk_A)
% 5.92/6.10        | ((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10        | (v2_struct_0 @ sk_C)
% 5.92/6.10        | (r1_orders_2 @ sk_A @ 
% 5.92/6.10           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10           sk_B))),
% 5.92/6.10      inference('sup-', [status(thm)], ['178', '219'])).
% 5.92/6.10  thf('221', plain,
% 5.92/6.10      (((r1_orders_2 @ sk_A @ 
% 5.92/6.10         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10         sk_B)
% 5.92/6.10        | (v2_struct_0 @ sk_C)
% 5.92/6.10        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.10           sk_A)
% 5.92/6.10        | ((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.10      inference('simplify', [status(thm)], ['220'])).
% 5.92/6.10  thf('222', plain,
% 5.92/6.10      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.92/6.10         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 5.92/6.10          | ~ (r1_orders_2 @ X11 @ X8 @ X10))),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.92/6.10  thf('223', plain,
% 5.92/6.10      (![X0 : $i]:
% 5.92/6.10         (((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.10             sk_B @ sk_A)
% 5.92/6.10          | (v2_struct_0 @ sk_C)
% 5.92/6.10          | (zip_tseitin_0 @ 
% 5.92/6.10             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10             X0 @ sk_B @ sk_A))),
% 5.92/6.10      inference('sup-', [status(thm)], ['221', '222'])).
% 5.92/6.10  thf('224', plain,
% 5.92/6.10      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.92/6.10         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.92/6.10          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.10  thf('225', plain,
% 5.92/6.10      (![X0 : $i]:
% 5.92/6.10         ((v2_struct_0 @ sk_C)
% 5.92/6.10          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.10             sk_B @ sk_A)
% 5.92/6.10          | ((sk_B)
% 5.92/6.10              = (k2_yellow_0 @ sk_A @ 
% 5.92/6.10                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10          | (zip_tseitin_1 @ 
% 5.92/6.10             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.92/6.10             X0 @ sk_B @ sk_A))),
% 5.92/6.10      inference('sup-', [status(thm)], ['223', '224'])).
% 5.92/6.10  thf('226', plain,
% 5.92/6.10      (![X0 : $i]:
% 5.92/6.10         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 5.92/6.10          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.92/6.10          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 5.92/6.10      inference('demod', [status(thm)], ['90', '91'])).
% 5.92/6.10  thf('227', plain,
% 5.92/6.10      ((((sk_B)
% 5.92/6.10          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.10           sk_A)
% 5.92/6.10        | (v2_struct_0 @ sk_C)
% 5.92/6.10        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.10           sk_A)
% 5.92/6.10        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.10             sk_B))),
% 5.92/6.10      inference('sup-', [status(thm)], ['225', '226'])).
% 5.92/6.10  thf('228', plain,
% 5.92/6.10      ((~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.92/6.10           sk_B)
% 5.92/6.10        | (v2_struct_0 @ sk_C)
% 5.92/6.10        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.10           sk_A)
% 5.92/6.10        | ((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.10      inference('simplify', [status(thm)], ['227'])).
% 5.92/6.10  thf('229', plain,
% 5.92/6.10      ((((sk_B)
% 5.92/6.10          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10        | ((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.10           sk_A)
% 5.92/6.10        | (v2_struct_0 @ sk_C))),
% 5.92/6.10      inference('sup-', [status(thm)], ['177', '228'])).
% 5.92/6.10  thf('230', plain,
% 5.92/6.10      (((v2_struct_0 @ sk_C)
% 5.92/6.10        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.10           sk_A)
% 5.92/6.10        | ((sk_B)
% 5.92/6.10            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.92/6.10      inference('simplify', [status(thm)], ['229'])).
% 5.92/6.10  thf('231', plain, (~ (v2_struct_0 @ sk_C)),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.10  thf('232', plain,
% 5.92/6.10      ((((sk_B)
% 5.92/6.10          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.92/6.10        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.92/6.10           sk_A))),
% 5.92/6.10      inference('clc', [status(thm)], ['230', '231'])).
% 5.92/6.10  thf('233', plain,
% 5.92/6.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.92/6.10         (((X18) = (k2_yellow_0 @ X16 @ X17))
% 5.92/6.10          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.92/6.10  thf('234', plain,
% 5.92/6.10      (((sk_B)
% 5.92/6.10         = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))),
% 5.92/6.10      inference('clc', [status(thm)], ['232', '233'])).
% 5.92/6.10  thf('235', plain,
% 5.92/6.10      ((((sk_B) = (k5_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 5.92/6.10        | ~ (v1_lattice3 @ sk_A)
% 5.92/6.10        | ~ (v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))
% 5.92/6.10        | ~ (l1_waybel_9 @ sk_A))),
% 5.92/6.10      inference('sup+', [status(thm)], ['13', '234'])).
% 5.92/6.10  thf('236', plain, ((v1_lattice3 @ sk_A)),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.10  thf('237', plain,
% 5.92/6.10      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 5.92/6.10        (k1_zfmisc_1 @ 
% 5.92/6.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 5.92/6.10      inference('demod', [status(thm)], ['35', '40'])).
% 5.92/6.10  thf(cc1_relset_1, axiom,
% 5.92/6.10    (![A:$i,B:$i,C:$i]:
% 5.92/6.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.92/6.10       ( v1_relat_1 @ C ) ))).
% 5.92/6.10  thf('238', plain,
% 5.92/6.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.92/6.10         ((v1_relat_1 @ X0)
% 5.92/6.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 5.92/6.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.92/6.10  thf('239', plain, ((v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))),
% 5.92/6.10      inference('sup-', [status(thm)], ['237', '238'])).
% 5.92/6.10  thf('240', plain, ((l1_waybel_9 @ sk_A)),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.10  thf('241', plain,
% 5.92/6.10      (((sk_B) = (k5_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 5.92/6.10      inference('demod', [status(thm)], ['235', '236', '239', '240'])).
% 5.92/6.10  thf('242', plain,
% 5.92/6.10      ((((sk_B) = (k1_waybel_9 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 5.92/6.10      inference('sup+', [status(thm)], ['7', '241'])).
% 5.92/6.10  thf('243', plain, (((sk_B) != (k1_waybel_9 @ sk_A @ sk_C))),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.10  thf('244', plain, ((v2_struct_0 @ sk_A)),
% 5.92/6.10      inference('simplify_reflect-', [status(thm)], ['242', '243'])).
% 5.92/6.10  thf('245', plain,
% 5.92/6.10      (![X7 : $i]:
% 5.92/6.10         (~ (v1_lattice3 @ X7) | ~ (v2_struct_0 @ X7) | ~ (l1_orders_2 @ X7))),
% 5.92/6.10      inference('cnf', [status(esa)], [cc1_lattice3])).
% 5.92/6.10  thf('246', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 5.92/6.10      inference('sup-', [status(thm)], ['244', '245'])).
% 5.92/6.10  thf('247', plain, ((v1_lattice3 @ sk_A)),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.10  thf('248', plain, (~ (l1_orders_2 @ sk_A)),
% 5.92/6.10      inference('demod', [status(thm)], ['246', '247'])).
% 5.92/6.10  thf('249', plain, (~ (l1_waybel_9 @ sk_A)),
% 5.92/6.10      inference('sup-', [status(thm)], ['0', '248'])).
% 5.92/6.10  thf('250', plain, ((l1_waybel_9 @ sk_A)),
% 5.92/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.10  thf('251', plain, ($false), inference('demod', [status(thm)], ['249', '250'])).
% 5.92/6.10  
% 5.92/6.10  % SZS output end Refutation
% 5.92/6.10  
% 5.92/6.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
