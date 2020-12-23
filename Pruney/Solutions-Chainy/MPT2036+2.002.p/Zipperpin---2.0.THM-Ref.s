%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rYn3tjDdfN

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:34 EST 2020

% Result     : Theorem 3.30s
% Output     : Refutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  348 (6273 expanded)
%              Number of leaves         :   65 (1888 expanded)
%              Depth                    :   96
%              Number of atoms          : 5431 (189099 expanded)
%              Number of equality atoms :  111 (3098 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v10_waybel_0_type,type,(
    v10_waybel_0: $i > $i > $o )).

thf(k1_waybel_2_type,type,(
    k1_waybel_2: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_yellow_2_type,type,(
    k4_yellow_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X33: $i] :
      ( ( l1_orders_2 @ X33 )
      | ~ ( l1_waybel_9 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('1',plain,(
    ! [X33: $i] :
      ( ( l1_orders_2 @ X33 )
      | ~ ( l1_waybel_9 @ X33 ) ) ),
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

thf('2',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_waybel_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( k1_waybel_2 @ A @ B )
            = ( k4_yellow_2 @ A @ ( u1_waybel_0 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_waybel_0 @ X29 @ X30 )
      | ( ( k1_waybel_2 @ X30 @ X29 )
        = ( k4_yellow_2 @ X30 @ ( u1_waybel_0 @ X30 @ X29 ) ) )
      | ~ ( l1_orders_2 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_2])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_waybel_2 @ sk_A @ sk_C )
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k1_waybel_2 @ sk_A @ sk_C )
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_waybel_2 @ sk_A @ sk_C )
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X33: $i] :
      ( ( l1_orders_2 @ X33 )
      | ~ ( l1_waybel_9 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(d5_yellow_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_yellow_2 @ A @ B )
            = ( k1_yellow_0 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k4_yellow_2 @ X32 @ X31 )
        = ( k1_yellow_0 @ X32 @ ( k2_relat_1 @ X31 ) ) )
      | ~ ( l1_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_2])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ~ ( v1_lattice3 @ X10 )
      | ~ ( v2_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k4_yellow_2 @ X0 @ X1 )
        = ( k1_yellow_0 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k4_yellow_2 @ X0 @ X1 )
        = ( k1_yellow_0 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ( ( k4_yellow_2 @ X0 @ X1 )
        = ( k1_yellow_0 @ X0 @ ( k2_relat_1 @ X1 ) ) )
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

thf('18',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( r2_lattice3 @ X35 @ ( k2_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) @ ( u1_waybel_0 @ X35 @ X34 ) ) @ X36 )
      | ( X37 != X36 )
      | ~ ( r3_waybel_9 @ X35 @ X34 @ X37 )
      | ~ ( v10_waybel_0 @ X34 @ X35 )
      | ( m1_subset_1 @ ( sk_E @ X35 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_waybel_9 @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[l48_waybel_9])).

thf('19',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v2_pre_topc @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( l1_waybel_9 @ X35 )
      | ( m1_subset_1 @ ( sk_E @ X35 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v10_waybel_0 @ X34 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X34 @ X36 )
      | ( r2_lattice3 @ X35 @ ( k2_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) @ ( u1_waybel_0 @ X35 @ X34 ) ) @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_waybel_0 @ X34 @ X35 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
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
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_B )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25','26','27','28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v10_waybel_0 @ sk_C @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( v7_waybel_0 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,(
    v10_waybel_0 @ sk_C @ sk_A ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( l1_waybel_0 @ X28 @ X27 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X33: $i] :
      ( ( l1_orders_2 @ X33 )
      | ~ ( l1_waybel_9 @ X33 ) ) ),
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
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['31','32','43','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(t30_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) )
               => ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    ! [X33: $i] :
      ( ( l1_orders_2 @ X33 )
      | ~ ( l1_waybel_9 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_yellow_0 @ A @ C ) )
        & ( r1_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ B @ D ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k1_yellow_0 @ A @ C ) )
                  & ( r1_yellow_0 @ A @ C ) )
               => ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_lattice3 @ X23 @ X26 @ X22 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X26 @ X22 @ X23 ) @ X26 @ X22 @ X23 )
      | ( zip_tseitin_2 @ X26 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('65',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_lattice3 @ X14 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_lattice3 @ X0 @ X2 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('72',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_lattice3 @ X14 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('76',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

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

thf('77',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v7_waybel_0 @ X38 )
      | ~ ( l1_waybel_0 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r2_lattice3 @ X39 @ ( k2_relset_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X39 ) @ ( u1_waybel_0 @ X39 @ X38 ) ) @ X41 )
      | ( r3_orders_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ( X42 != X40 )
      | ~ ( r3_waybel_9 @ X39 @ X38 @ X42 )
      | ( m1_subset_1 @ ( sk_E_1 @ X39 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_waybel_9 @ X39 )
      | ~ ( v1_compts_1 @ X39 )
      | ~ ( v2_lattice3 @ X39 )
      | ~ ( v1_lattice3 @ X39 )
      | ~ ( v5_orders_2 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ~ ( v3_orders_2 @ X39 )
      | ~ ( v8_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[l49_waybel_9])).

thf('78',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v2_pre_topc @ X39 )
      | ~ ( v8_pre_topc @ X39 )
      | ~ ( v3_orders_2 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ~ ( v5_orders_2 @ X39 )
      | ~ ( v1_lattice3 @ X39 )
      | ~ ( v2_lattice3 @ X39 )
      | ~ ( v1_compts_1 @ X39 )
      | ~ ( l1_waybel_9 @ X39 )
      | ( m1_subset_1 @ ( sk_E_1 @ X39 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( r3_waybel_9 @ X39 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ( r3_orders_2 @ X39 @ X40 @ X41 )
      | ~ ( r2_lattice3 @ X39 @ ( k2_relset_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X39 ) @ ( u1_waybel_0 @ X39 @ X38 ) ) @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_waybel_0 @ X38 @ X39 )
      | ~ ( v7_waybel_0 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_C )
      | ~ ( v7_waybel_0 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
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
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84','85','86','87','88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X2 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','96'])).

thf('98',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r3_orders_2 @ sk_A @ sk_B @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(eq_fact,[status(thm)],['99'])).

thf('101',plain,(
    ! [X43: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X43 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('104',plain,
    ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['72','104'])).

thf('106',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('107',plain,(
    ! [X33: $i] :
      ( ( l1_orders_2 @ X33 )
      | ~ ( l1_waybel_9 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('108',plain,(
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

thf('109',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r3_orders_2 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','115'])).

thf('117',plain,
    ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','116'])).

thf('118',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( r1_orders_2 @ X14 @ X13 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('124',plain,
    ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('129',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v7_waybel_0 @ X38 )
      | ~ ( l1_waybel_0 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r2_lattice3 @ X39 @ ( k2_relset_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X39 ) @ ( u1_waybel_0 @ X39 @ X38 ) ) @ X41 )
      | ( r3_orders_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ( X42 != X40 )
      | ~ ( r3_waybel_9 @ X39 @ X38 @ X42 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X39 @ ( sk_E_1 @ X39 ) ) @ X39 @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_waybel_9 @ X39 )
      | ~ ( v1_compts_1 @ X39 )
      | ~ ( v2_lattice3 @ X39 )
      | ~ ( v1_lattice3 @ X39 )
      | ~ ( v5_orders_2 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ~ ( v3_orders_2 @ X39 )
      | ~ ( v8_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[l49_waybel_9])).

thf('130',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v2_pre_topc @ X39 )
      | ~ ( v8_pre_topc @ X39 )
      | ~ ( v3_orders_2 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ~ ( v5_orders_2 @ X39 )
      | ~ ( v1_lattice3 @ X39 )
      | ~ ( v2_lattice3 @ X39 )
      | ~ ( v1_compts_1 @ X39 )
      | ~ ( l1_waybel_9 @ X39 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X39 @ ( sk_E_1 @ X39 ) ) @ X39 @ X39 )
      | ~ ( r3_waybel_9 @ X39 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ( r3_orders_2 @ X39 @ X40 @ X41 )
      | ~ ( r2_lattice3 @ X39 @ ( k2_relset_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X39 ) @ ( u1_waybel_0 @ X39 @ X38 ) ) @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_waybel_0 @ X38 @ X39 )
      | ~ ( v7_waybel_0 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_C )
      | ~ ( v7_waybel_0 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
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
    inference('sup-',[status(thm)],['128','130'])).

thf('132',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135','136','137','138','139','140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['127','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','115'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( r1_orders_2 @ X14 @ X13 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','163'])).

thf('165',plain,
    ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X21
        = ( k1_yellow_0 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_2 @ X20 @ X21 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('167',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X43: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X43 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( r2_lattice3 @ X35 @ ( k2_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) @ ( u1_waybel_0 @ X35 @ X34 ) ) @ X36 )
      | ( X37 != X36 )
      | ~ ( r3_waybel_9 @ X35 @ X34 @ X37 )
      | ~ ( v10_waybel_0 @ X34 @ X35 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X35 @ ( sk_E @ X35 ) ) @ X35 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_waybel_9 @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[l48_waybel_9])).

thf('171',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v2_pre_topc @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( l1_waybel_9 @ X35 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X35 @ ( sk_E @ X35 ) ) @ X35 @ X35 )
      | ~ ( v10_waybel_0 @ X34 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X34 @ X36 )
      | ( r2_lattice3 @ X35 @ ( k2_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) @ ( u1_waybel_0 @ X35 @ X34 ) ) @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_waybel_0 @ X34 @ X35 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
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
    inference('sup-',[status(thm)],['169','171'])).

thf('173',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v10_waybel_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173','174','175','176','177','178','179','180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','182'])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ~ ( v7_waybel_0 @ sk_C )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ~ ( v10_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['14','183'])).

thf('185',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('189',plain,(
    v10_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['184','185','186','187','188','189'])).

thf('191',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ( ( k4_yellow_2 @ X0 @ X1 )
        = ( k1_yellow_0 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('194',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('195',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_lattice3 @ X14 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('197',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('198',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(eq_fact,[status(thm)],['99'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('201',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['198','201'])).

thf('203',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','61'])).

thf('206',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('208',plain,
    ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['203','209'])).

thf('211',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( r1_orders_2 @ X14 @ X13 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('217',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['197','218'])).

thf('220',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X21
        = ( k1_yellow_0 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_2 @ X20 @ X21 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('222',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ! [X43: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X43 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135','136','137','138','139','140','141','142','143'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X2 @ sk_A )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['196','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['195','229'])).

thf('231',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['194','232'])).

thf('234',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) )
      | ~ ( l1_waybel_9 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['193','233'])).

thf('235',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('237',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('238',plain,(
    v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['234','235','238','239'])).

thf('241',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('242',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ X1 )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
      | ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(eq_fact,[status(thm)],['242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['192','245'])).

thf('247',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['208'])).

thf('249',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( r1_orders_2 @ X14 @ X13 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( sk_B
        = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('256',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['191','257'])).

thf('259',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X21
        = ( k1_yellow_0 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_2 @ X20 @ X21 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( sk_B
      = ( k1_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    | ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['13','262'])).

thf('264',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('266',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['263','264','265','266'])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( sk_B
      = ( k4_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,
    ( ( sk_B
      = ( k1_waybel_2 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','270'])).

thf('272',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k1_waybel_2 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,(
    sk_B
 != ( k1_waybel_2 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['272','273'])).

thf('275',plain,(
    ! [X10: $i] :
      ( ~ ( v1_lattice3 @ X10 )
      | ~ ( v2_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('276',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['276','277'])).

thf('279',plain,(
    ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','278'])).

thf('280',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    $false ),
    inference(demod,[status(thm)],['279','280'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rYn3tjDdfN
% 0.13/0.37  % Computer   : n022.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 12:58:11 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 3.30/3.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.30/3.55  % Solved by: fo/fo7.sh
% 3.30/3.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.30/3.55  % done 1710 iterations in 3.097s
% 3.30/3.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.30/3.55  % SZS output start Refutation
% 3.30/3.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.30/3.55  thf(sk_A_type, type, sk_A: $i).
% 3.30/3.55  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 3.30/3.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.30/3.55  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 3.30/3.55  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 3.30/3.55  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 3.30/3.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 3.30/3.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.30/3.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.30/3.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.30/3.55  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 3.30/3.55  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 3.30/3.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 3.30/3.55  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 3.30/3.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.30/3.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.30/3.55  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 3.30/3.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.30/3.55  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 3.30/3.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 3.30/3.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 3.30/3.55  thf(v10_waybel_0_type, type, v10_waybel_0: $i > $i > $o).
% 3.30/3.55  thf(k1_waybel_2_type, type, k1_waybel_2: $i > $i > $i).
% 3.30/3.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 3.30/3.55  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 3.30/3.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.30/3.55  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 3.30/3.55  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 3.30/3.55  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 3.30/3.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.30/3.55  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 3.30/3.55  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 3.30/3.55  thf(sk_B_type, type, sk_B: $i).
% 3.30/3.55  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 3.30/3.55  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 3.30/3.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.30/3.55  thf(sk_E_type, type, sk_E: $i > $i).
% 3.30/3.55  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 3.30/3.55  thf(sk_C_type, type, sk_C: $i).
% 3.30/3.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.30/3.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.30/3.55  thf(k4_yellow_2_type, type, k4_yellow_2: $i > $i > $i).
% 3.30/3.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.30/3.55  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 3.30/3.55  thf(dt_l1_waybel_9, axiom,
% 3.30/3.55    (![A:$i]:
% 3.30/3.55     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 3.30/3.55  thf('0', plain, (![X33 : $i]: ((l1_orders_2 @ X33) | ~ (l1_waybel_9 @ X33))),
% 3.30/3.55      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 3.30/3.55  thf('1', plain, (![X33 : $i]: ((l1_orders_2 @ X33) | ~ (l1_waybel_9 @ X33))),
% 3.30/3.55      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 3.30/3.55  thf(t35_waybel_9, conjecture,
% 3.30/3.55    (![A:$i]:
% 3.30/3.55     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 3.30/3.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 3.30/3.55         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 3.30/3.55       ( ![B:$i]:
% 3.30/3.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55           ( ![C:$i]:
% 3.30/3.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 3.30/3.55                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 3.30/3.55               ( ( ( ![D:$i]:
% 3.30/3.55                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55                       ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 3.30/3.55                   ( v10_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 3.30/3.55                 ( ( B ) = ( k1_waybel_2 @ A @ C ) ) ) ) ) ) ) ))).
% 3.30/3.55  thf(zf_stmt_0, negated_conjecture,
% 3.30/3.55    (~( ![A:$i]:
% 3.30/3.55        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 3.30/3.55            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 3.30/3.55            ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 3.30/3.55          ( ![B:$i]:
% 3.30/3.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55              ( ![C:$i]:
% 3.30/3.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 3.30/3.55                    ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 3.30/3.55                  ( ( ( ![D:$i]:
% 3.30/3.55                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55                          ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 3.30/3.55                      ( v10_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 3.30/3.55                    ( ( B ) = ( k1_waybel_2 @ A @ C ) ) ) ) ) ) ) ) )),
% 3.30/3.55    inference('cnf.neg', [status(esa)], [t35_waybel_9])).
% 3.30/3.55  thf('2', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf(d1_waybel_2, axiom,
% 3.30/3.55    (![A:$i]:
% 3.30/3.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 3.30/3.55       ( ![B:$i]:
% 3.30/3.55         ( ( l1_waybel_0 @ B @ A ) =>
% 3.30/3.55           ( ( k1_waybel_2 @ A @ B ) =
% 3.30/3.55             ( k4_yellow_2 @ A @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 3.30/3.55  thf('3', plain,
% 3.30/3.55      (![X29 : $i, X30 : $i]:
% 3.30/3.55         (~ (l1_waybel_0 @ X29 @ X30)
% 3.30/3.55          | ((k1_waybel_2 @ X30 @ X29)
% 3.30/3.55              = (k4_yellow_2 @ X30 @ (u1_waybel_0 @ X30 @ X29)))
% 3.30/3.55          | ~ (l1_orders_2 @ X30)
% 3.30/3.55          | (v2_struct_0 @ X30))),
% 3.30/3.55      inference('cnf', [status(esa)], [d1_waybel_2])).
% 3.30/3.55  thf('4', plain,
% 3.30/3.55      (((v2_struct_0 @ sk_A)
% 3.30/3.55        | ~ (l1_orders_2 @ sk_A)
% 3.30/3.55        | ((k1_waybel_2 @ sk_A @ sk_C)
% 3.30/3.55            = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C))))),
% 3.30/3.55      inference('sup-', [status(thm)], ['2', '3'])).
% 3.30/3.55  thf('5', plain,
% 3.30/3.55      ((~ (l1_waybel_9 @ sk_A)
% 3.30/3.55        | ((k1_waybel_2 @ sk_A @ sk_C)
% 3.30/3.55            = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['1', '4'])).
% 3.30/3.55  thf('6', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('7', plain,
% 3.30/3.55      ((((k1_waybel_2 @ sk_A @ sk_C)
% 3.30/3.55          = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('demod', [status(thm)], ['5', '6'])).
% 3.30/3.55  thf('8', plain, (![X33 : $i]: ((l1_orders_2 @ X33) | ~ (l1_waybel_9 @ X33))),
% 3.30/3.55      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 3.30/3.55  thf(d5_yellow_2, axiom,
% 3.30/3.55    (![A:$i]:
% 3.30/3.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 3.30/3.55       ( ![B:$i]:
% 3.30/3.55         ( ( v1_relat_1 @ B ) =>
% 3.30/3.55           ( ( k4_yellow_2 @ A @ B ) = ( k1_yellow_0 @ A @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 3.30/3.55  thf('9', plain,
% 3.30/3.55      (![X31 : $i, X32 : $i]:
% 3.30/3.55         (~ (v1_relat_1 @ X31)
% 3.30/3.55          | ((k4_yellow_2 @ X32 @ X31)
% 3.30/3.55              = (k1_yellow_0 @ X32 @ (k2_relat_1 @ X31)))
% 3.30/3.55          | ~ (l1_orders_2 @ X32)
% 3.30/3.55          | (v2_struct_0 @ X32))),
% 3.30/3.55      inference('cnf', [status(esa)], [d5_yellow_2])).
% 3.30/3.55  thf(cc1_lattice3, axiom,
% 3.30/3.55    (![A:$i]:
% 3.30/3.55     ( ( l1_orders_2 @ A ) =>
% 3.30/3.55       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 3.30/3.55  thf('10', plain,
% 3.30/3.55      (![X10 : $i]:
% 3.30/3.55         (~ (v1_lattice3 @ X10) | ~ (v2_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 3.30/3.55      inference('cnf', [status(esa)], [cc1_lattice3])).
% 3.30/3.55  thf('11', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         (~ (l1_orders_2 @ X0)
% 3.30/3.55          | ((k4_yellow_2 @ X0 @ X1) = (k1_yellow_0 @ X0 @ (k2_relat_1 @ X1)))
% 3.30/3.55          | ~ (v1_relat_1 @ X1)
% 3.30/3.55          | ~ (l1_orders_2 @ X0)
% 3.30/3.55          | ~ (v1_lattice3 @ X0))),
% 3.30/3.55      inference('sup-', [status(thm)], ['9', '10'])).
% 3.30/3.55  thf('12', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         (~ (v1_lattice3 @ X0)
% 3.30/3.55          | ~ (v1_relat_1 @ X1)
% 3.30/3.55          | ((k4_yellow_2 @ X0 @ X1) = (k1_yellow_0 @ X0 @ (k2_relat_1 @ X1)))
% 3.30/3.55          | ~ (l1_orders_2 @ X0))),
% 3.30/3.55      inference('simplify', [status(thm)], ['11'])).
% 3.30/3.55  thf('13', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         (~ (l1_waybel_9 @ X0)
% 3.30/3.55          | ((k4_yellow_2 @ X0 @ X1) = (k1_yellow_0 @ X0 @ (k2_relat_1 @ X1)))
% 3.30/3.55          | ~ (v1_relat_1 @ X1)
% 3.30/3.55          | ~ (v1_lattice3 @ X0))),
% 3.30/3.55      inference('sup-', [status(thm)], ['8', '12'])).
% 3.30/3.55  thf('14', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('16', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf(l48_waybel_9, axiom,
% 3.30/3.55    (![A:$i]:
% 3.30/3.55     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 3.30/3.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 3.30/3.55         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 3.30/3.55       ( ![B:$i]:
% 3.30/3.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 3.30/3.55             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 3.30/3.55           ( ![C:$i]:
% 3.30/3.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55               ( ![D:$i]:
% 3.30/3.55                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55                   ( ( ( ( C ) = ( D ) ) & 
% 3.30/3.55                       ( ![E:$i]:
% 3.30/3.55                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 3.30/3.55                       ( v10_waybel_0 @ B @ A ) & ( r3_waybel_9 @ A @ B @ C ) ) =>
% 3.30/3.55                     ( r2_lattice3 @
% 3.30/3.55                       A @ 
% 3.30/3.55                       ( k2_relset_1 @
% 3.30/3.55                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.30/3.55                         ( u1_waybel_0 @ A @ B ) ) @ 
% 3.30/3.55                       D ) ) ) ) ) ) ) ) ))).
% 3.30/3.55  thf('18', plain,
% 3.30/3.55      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.30/3.55         ((v2_struct_0 @ X34)
% 3.30/3.55          | ~ (v4_orders_2 @ X34)
% 3.30/3.55          | ~ (v7_waybel_0 @ X34)
% 3.30/3.55          | ~ (l1_waybel_0 @ X34 @ X35)
% 3.30/3.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 3.30/3.55          | (r2_lattice3 @ X35 @ 
% 3.30/3.55             (k2_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35) @ 
% 3.30/3.55              (u1_waybel_0 @ X35 @ X34)) @ 
% 3.30/3.55             X36)
% 3.30/3.55          | ((X37) != (X36))
% 3.30/3.55          | ~ (r3_waybel_9 @ X35 @ X34 @ X37)
% 3.30/3.55          | ~ (v10_waybel_0 @ X34 @ X35)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ X35) @ (u1_struct_0 @ X35))
% 3.30/3.55          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 3.30/3.55          | ~ (l1_waybel_9 @ X35)
% 3.30/3.55          | ~ (v1_compts_1 @ X35)
% 3.30/3.55          | ~ (v2_lattice3 @ X35)
% 3.30/3.55          | ~ (v1_lattice3 @ X35)
% 3.30/3.55          | ~ (v5_orders_2 @ X35)
% 3.30/3.55          | ~ (v4_orders_2 @ X35)
% 3.30/3.55          | ~ (v3_orders_2 @ X35)
% 3.30/3.55          | ~ (v8_pre_topc @ X35)
% 3.30/3.55          | ~ (v2_pre_topc @ X35))),
% 3.30/3.55      inference('cnf', [status(esa)], [l48_waybel_9])).
% 3.30/3.55  thf('19', plain,
% 3.30/3.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.30/3.55         (~ (v2_pre_topc @ X35)
% 3.30/3.55          | ~ (v8_pre_topc @ X35)
% 3.30/3.55          | ~ (v3_orders_2 @ X35)
% 3.30/3.55          | ~ (v4_orders_2 @ X35)
% 3.30/3.55          | ~ (v5_orders_2 @ X35)
% 3.30/3.55          | ~ (v1_lattice3 @ X35)
% 3.30/3.55          | ~ (v2_lattice3 @ X35)
% 3.30/3.55          | ~ (v1_compts_1 @ X35)
% 3.30/3.55          | ~ (l1_waybel_9 @ X35)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ X35) @ (u1_struct_0 @ X35))
% 3.30/3.55          | ~ (v10_waybel_0 @ X34 @ X35)
% 3.30/3.55          | ~ (r3_waybel_9 @ X35 @ X34 @ X36)
% 3.30/3.55          | (r2_lattice3 @ X35 @ 
% 3.30/3.55             (k2_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35) @ 
% 3.30/3.55              (u1_waybel_0 @ X35 @ X34)) @ 
% 3.30/3.55             X36)
% 3.30/3.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 3.30/3.55          | ~ (l1_waybel_0 @ X34 @ X35)
% 3.30/3.55          | ~ (v7_waybel_0 @ X34)
% 3.30/3.55          | ~ (v4_orders_2 @ X34)
% 3.30/3.55          | (v2_struct_0 @ X34))),
% 3.30/3.55      inference('simplify', [status(thm)], ['18'])).
% 3.30/3.55  thf('20', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((v2_struct_0 @ X0)
% 3.30/3.55          | ~ (v4_orders_2 @ X0)
% 3.30/3.55          | ~ (v7_waybel_0 @ X0)
% 3.30/3.55          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 3.30/3.55          | (r2_lattice3 @ sk_A @ 
% 3.30/3.55             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55              (u1_waybel_0 @ sk_A @ X0)) @ 
% 3.30/3.55             sk_B)
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 3.30/3.55          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | ~ (l1_waybel_9 @ sk_A)
% 3.30/3.55          | ~ (v1_compts_1 @ sk_A)
% 3.30/3.55          | ~ (v2_lattice3 @ sk_A)
% 3.30/3.55          | ~ (v1_lattice3 @ sk_A)
% 3.30/3.55          | ~ (v5_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v4_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v3_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v8_pre_topc @ sk_A)
% 3.30/3.55          | ~ (v2_pre_topc @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['17', '19'])).
% 3.30/3.55  thf('21', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('22', plain, ((v1_compts_1 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('23', plain, ((v2_lattice3 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('24', plain, ((v1_lattice3 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('25', plain, ((v5_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('26', plain, ((v4_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('27', plain, ((v3_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('28', plain, ((v8_pre_topc @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('30', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((v2_struct_0 @ X0)
% 3.30/3.55          | ~ (v4_orders_2 @ X0)
% 3.30/3.55          | ~ (v7_waybel_0 @ X0)
% 3.30/3.55          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 3.30/3.55          | (r2_lattice3 @ sk_A @ 
% 3.30/3.55             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55              (u1_waybel_0 @ sk_A @ X0)) @ 
% 3.30/3.55             sk_B)
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 3.30/3.55          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('demod', [status(thm)],
% 3.30/3.55                ['20', '21', '22', '23', '24', '25', '26', '27', '28', '29'])).
% 3.30/3.55  thf('31', plain,
% 3.30/3.55      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | ~ (v10_waybel_0 @ sk_C @ sk_A)
% 3.30/3.55        | (r2_lattice3 @ sk_A @ 
% 3.30/3.55           (k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55            (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55           sk_B)
% 3.30/3.55        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 3.30/3.55        | ~ (v7_waybel_0 @ sk_C)
% 3.30/3.55        | ~ (v4_orders_2 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_C))),
% 3.30/3.55      inference('sup-', [status(thm)], ['16', '30'])).
% 3.30/3.55  thf('32', plain, ((v10_waybel_0 @ sk_C @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('33', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf(dt_u1_waybel_0, axiom,
% 3.30/3.55    (![A:$i,B:$i]:
% 3.30/3.55     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 3.30/3.55       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 3.30/3.55         ( v1_funct_2 @
% 3.30/3.55           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 3.30/3.55         ( m1_subset_1 @
% 3.30/3.55           ( u1_waybel_0 @ A @ B ) @ 
% 3.30/3.55           ( k1_zfmisc_1 @
% 3.30/3.55             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.30/3.55  thf('34', plain,
% 3.30/3.55      (![X27 : $i, X28 : $i]:
% 3.30/3.55         (~ (l1_struct_0 @ X27)
% 3.30/3.55          | ~ (l1_waybel_0 @ X28 @ X27)
% 3.30/3.55          | (m1_subset_1 @ (u1_waybel_0 @ X27 @ X28) @ 
% 3.30/3.55             (k1_zfmisc_1 @ 
% 3.30/3.55              (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27)))))),
% 3.30/3.55      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 3.30/3.55  thf('35', plain,
% 3.30/3.55      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 3.30/3.55         (k1_zfmisc_1 @ 
% 3.30/3.55          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 3.30/3.55        | ~ (l1_struct_0 @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['33', '34'])).
% 3.30/3.55  thf('36', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('37', plain,
% 3.30/3.55      (![X33 : $i]: ((l1_orders_2 @ X33) | ~ (l1_waybel_9 @ X33))),
% 3.30/3.55      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 3.30/3.55  thf(dt_l1_orders_2, axiom,
% 3.30/3.55    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 3.30/3.55  thf('38', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 3.30/3.55      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 3.30/3.55  thf('39', plain, (![X0 : $i]: (~ (l1_waybel_9 @ X0) | (l1_struct_0 @ X0))),
% 3.30/3.55      inference('sup-', [status(thm)], ['37', '38'])).
% 3.30/3.55  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 3.30/3.55      inference('sup-', [status(thm)], ['36', '39'])).
% 3.30/3.55  thf('41', plain,
% 3.30/3.55      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 3.30/3.55        (k1_zfmisc_1 @ 
% 3.30/3.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.30/3.55      inference('demod', [status(thm)], ['35', '40'])).
% 3.30/3.55  thf(redefinition_k2_relset_1, axiom,
% 3.30/3.55    (![A:$i,B:$i,C:$i]:
% 3.30/3.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.30/3.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.30/3.55  thf('42', plain,
% 3.30/3.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.30/3.55         (((k2_relset_1 @ X4 @ X5 @ X3) = (k2_relat_1 @ X3))
% 3.30/3.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 3.30/3.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.30/3.55  thf('43', plain,
% 3.30/3.55      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55         (u1_waybel_0 @ sk_A @ sk_C))
% 3.30/3.55         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['41', '42'])).
% 3.30/3.55  thf('44', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('45', plain, ((v7_waybel_0 @ sk_C)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('46', plain, ((v4_orders_2 @ sk_C)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('47', plain,
% 3.30/3.55      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55           sk_B)
% 3.30/3.55        | (v2_struct_0 @ sk_C))),
% 3.30/3.55      inference('demod', [status(thm)], ['31', '32', '43', '44', '45', '46'])).
% 3.30/3.55  thf('48', plain, (~ (v2_struct_0 @ sk_C)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('49', plain,
% 3.30/3.55      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('clc', [status(thm)], ['47', '48'])).
% 3.30/3.55  thf('50', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('51', plain,
% 3.30/3.55      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('clc', [status(thm)], ['47', '48'])).
% 3.30/3.55  thf(t30_yellow_0, axiom,
% 3.30/3.55    (![A:$i]:
% 3.30/3.55     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 3.30/3.55       ( ![B:$i]:
% 3.30/3.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55           ( ![C:$i]:
% 3.30/3.55             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 3.30/3.55                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 3.30/3.55                 ( ( ![D:$i]:
% 3.30/3.55                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 3.30/3.55                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 3.30/3.55                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 3.30/3.55               ( ( ( ![D:$i]:
% 3.30/3.55                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 3.30/3.55                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 3.30/3.55                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 3.30/3.55                 ( ( r1_yellow_0 @ A @ C ) & 
% 3.30/3.55                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 3.30/3.55  thf(zf_stmt_1, axiom,
% 3.30/3.55    (![D:$i,C:$i,B:$i,A:$i]:
% 3.30/3.55     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 3.30/3.55       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 3.30/3.55  thf('52', plain,
% 3.30/3.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.30/3.55         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 3.30/3.55          | (m1_subset_1 @ X15 @ (u1_struct_0 @ X18)))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.55  thf('53', plain,
% 3.30/3.55      (![X33 : $i]: ((l1_orders_2 @ X33) | ~ (l1_waybel_9 @ X33))),
% 3.30/3.55      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 3.30/3.55  thf('54', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 3.30/3.55  thf(zf_stmt_3, axiom,
% 3.30/3.55    (![C:$i,B:$i,A:$i]:
% 3.30/3.55     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 3.30/3.55       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 3.30/3.55  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 3.30/3.55  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 3.30/3.55  thf(zf_stmt_6, axiom,
% 3.30/3.55    (![D:$i,C:$i,B:$i,A:$i]:
% 3.30/3.55     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 3.30/3.55       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 3.30/3.55  thf(zf_stmt_7, axiom,
% 3.30/3.55    (![A:$i]:
% 3.30/3.55     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.30/3.55       ( ![B:$i]:
% 3.30/3.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55           ( ![C:$i]:
% 3.30/3.55             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 3.30/3.55                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 3.30/3.55                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 3.30/3.55               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 3.30/3.55                   ( r1_yellow_0 @ A @ C ) ) =>
% 3.30/3.55                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 3.30/3.55                   ( ![D:$i]:
% 3.30/3.55                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 3.30/3.55                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 3.30/3.55  thf('55', plain,
% 3.30/3.55      (![X22 : $i, X23 : $i, X26 : $i]:
% 3.30/3.55         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 3.30/3.55          | ~ (r2_lattice3 @ X23 @ X26 @ X22)
% 3.30/3.55          | ~ (zip_tseitin_1 @ (sk_D @ X26 @ X22 @ X23) @ X26 @ X22 @ X23)
% 3.30/3.55          | (zip_tseitin_2 @ X26 @ X22 @ X23)
% 3.30/3.55          | ~ (l1_orders_2 @ X23)
% 3.30/3.55          | ~ (v5_orders_2 @ X23))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_7])).
% 3.30/3.55  thf('56', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (v5_orders_2 @ sk_A)
% 3.30/3.55          | ~ (l1_orders_2 @ sk_A)
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 3.30/3.55      inference('sup-', [status(thm)], ['54', '55'])).
% 3.30/3.55  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('58', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (l1_orders_2 @ sk_A)
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 3.30/3.55      inference('demod', [status(thm)], ['56', '57'])).
% 3.30/3.55  thf('59', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (l1_waybel_9 @ sk_A)
% 3.30/3.55          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 3.30/3.55          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['53', '58'])).
% 3.30/3.55  thf('60', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('61', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 3.30/3.55          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.55  thf('62', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 3.30/3.55      inference('sup-', [status(thm)], ['52', '61'])).
% 3.30/3.55  thf('63', plain,
% 3.30/3.55      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (m1_subset_1 @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.55           (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['51', '62'])).
% 3.30/3.55  thf('64', plain,
% 3.30/3.55      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('clc', [status(thm)], ['47', '48'])).
% 3.30/3.55  thf('65', plain,
% 3.30/3.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.30/3.55         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 3.30/3.55          | (r2_lattice3 @ X14 @ X12 @ X11))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_6])).
% 3.30/3.55  thf('66', plain,
% 3.30/3.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.30/3.55         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 3.30/3.55          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.55  thf('67', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.30/3.55         ((r2_lattice3 @ X0 @ X2 @ X3) | (zip_tseitin_1 @ X3 @ X2 @ X1 @ X0))),
% 3.30/3.55      inference('sup-', [status(thm)], ['65', '66'])).
% 3.30/3.55  thf('68', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 3.30/3.55          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.55  thf('69', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((r2_lattice3 @ sk_A @ X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 3.30/3.55      inference('sup-', [status(thm)], ['67', '68'])).
% 3.30/3.55  thf('70', plain,
% 3.30/3.55      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['64', '69'])).
% 3.30/3.55  thf('71', plain,
% 3.30/3.55      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('clc', [status(thm)], ['47', '48'])).
% 3.30/3.55  thf('72', plain,
% 3.30/3.55      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('clc', [status(thm)], ['47', '48'])).
% 3.30/3.55  thf('73', plain,
% 3.30/3.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.30/3.55         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 3.30/3.55          | (m1_subset_1 @ X15 @ (u1_struct_0 @ X18)))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.55  thf('74', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('75', plain,
% 3.30/3.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.30/3.55         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 3.30/3.55          | (r2_lattice3 @ X14 @ X12 @ X11))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_6])).
% 3.30/3.55  thf('76', plain,
% 3.30/3.55      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55         (u1_waybel_0 @ sk_A @ sk_C))
% 3.30/3.55         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['41', '42'])).
% 3.30/3.55  thf(l49_waybel_9, axiom,
% 3.30/3.55    (![A:$i]:
% 3.30/3.55     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 3.30/3.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 3.30/3.55         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 3.30/3.55       ( ![B:$i]:
% 3.30/3.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 3.30/3.55             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 3.30/3.55           ( ![C:$i]:
% 3.30/3.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55               ( ![D:$i]:
% 3.30/3.55                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55                   ( ( ( ( C ) = ( D ) ) & 
% 3.30/3.55                       ( ![E:$i]:
% 3.30/3.55                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 3.30/3.55                       ( r3_waybel_9 @ A @ B @ C ) ) =>
% 3.30/3.55                     ( ![E:$i]:
% 3.30/3.55                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 3.30/3.55                         ( ( r2_lattice3 @
% 3.30/3.55                             A @ 
% 3.30/3.55                             ( k2_relset_1 @
% 3.30/3.55                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.30/3.55                               ( u1_waybel_0 @ A @ B ) ) @ 
% 3.30/3.55                             E ) =>
% 3.30/3.55                           ( r3_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.30/3.55  thf('77', plain,
% 3.30/3.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.30/3.55         ((v2_struct_0 @ X38)
% 3.30/3.55          | ~ (v4_orders_2 @ X38)
% 3.30/3.55          | ~ (v7_waybel_0 @ X38)
% 3.30/3.55          | ~ (l1_waybel_0 @ X38 @ X39)
% 3.30/3.55          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 3.30/3.55          | ~ (r2_lattice3 @ X39 @ 
% 3.30/3.55               (k2_relset_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X39) @ 
% 3.30/3.55                (u1_waybel_0 @ X39 @ X38)) @ 
% 3.30/3.55               X41)
% 3.30/3.55          | (r3_orders_2 @ X39 @ X40 @ X41)
% 3.30/3.55          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 3.30/3.55          | ((X42) != (X40))
% 3.30/3.55          | ~ (r3_waybel_9 @ X39 @ X38 @ X42)
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ X39) @ (u1_struct_0 @ X39))
% 3.30/3.55          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X39))
% 3.30/3.55          | ~ (l1_waybel_9 @ X39)
% 3.30/3.55          | ~ (v1_compts_1 @ X39)
% 3.30/3.55          | ~ (v2_lattice3 @ X39)
% 3.30/3.55          | ~ (v1_lattice3 @ X39)
% 3.30/3.55          | ~ (v5_orders_2 @ X39)
% 3.30/3.55          | ~ (v4_orders_2 @ X39)
% 3.30/3.55          | ~ (v3_orders_2 @ X39)
% 3.30/3.55          | ~ (v8_pre_topc @ X39)
% 3.30/3.55          | ~ (v2_pre_topc @ X39))),
% 3.30/3.55      inference('cnf', [status(esa)], [l49_waybel_9])).
% 3.30/3.55  thf('78', plain,
% 3.30/3.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.30/3.55         (~ (v2_pre_topc @ X39)
% 3.30/3.55          | ~ (v8_pre_topc @ X39)
% 3.30/3.55          | ~ (v3_orders_2 @ X39)
% 3.30/3.55          | ~ (v4_orders_2 @ X39)
% 3.30/3.55          | ~ (v5_orders_2 @ X39)
% 3.30/3.55          | ~ (v1_lattice3 @ X39)
% 3.30/3.55          | ~ (v2_lattice3 @ X39)
% 3.30/3.55          | ~ (v1_compts_1 @ X39)
% 3.30/3.55          | ~ (l1_waybel_9 @ X39)
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ X39) @ (u1_struct_0 @ X39))
% 3.30/3.55          | ~ (r3_waybel_9 @ X39 @ X38 @ X40)
% 3.30/3.55          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 3.30/3.55          | (r3_orders_2 @ X39 @ X40 @ X41)
% 3.30/3.55          | ~ (r2_lattice3 @ X39 @ 
% 3.30/3.55               (k2_relset_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X39) @ 
% 3.30/3.55                (u1_waybel_0 @ X39 @ X38)) @ 
% 3.30/3.55               X41)
% 3.30/3.55          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 3.30/3.55          | ~ (l1_waybel_0 @ X38 @ X39)
% 3.30/3.55          | ~ (v7_waybel_0 @ X38)
% 3.30/3.55          | ~ (v4_orders_2 @ X38)
% 3.30/3.55          | (v2_struct_0 @ X38))),
% 3.30/3.55      inference('simplify', [status(thm)], ['77'])).
% 3.30/3.55  thf('79', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             X0)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | ~ (v4_orders_2 @ sk_C)
% 3.30/3.55          | ~ (v7_waybel_0 @ sk_C)
% 3.30/3.55          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 3.30/3.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | ~ (l1_waybel_9 @ sk_A)
% 3.30/3.55          | ~ (v1_compts_1 @ sk_A)
% 3.30/3.55          | ~ (v2_lattice3 @ sk_A)
% 3.30/3.55          | ~ (v1_lattice3 @ sk_A)
% 3.30/3.55          | ~ (v5_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v4_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v3_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v8_pre_topc @ sk_A)
% 3.30/3.55          | ~ (v2_pre_topc @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['76', '78'])).
% 3.30/3.55  thf('80', plain, ((v4_orders_2 @ sk_C)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('81', plain, ((v7_waybel_0 @ sk_C)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('82', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('83', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('84', plain, ((v1_compts_1 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('85', plain, ((v2_lattice3 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('86', plain, ((v1_lattice3 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('87', plain, ((v5_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('88', plain, ((v4_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('89', plain, ((v3_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('90', plain, ((v8_pre_topc @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('92', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             X0)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('demod', [status(thm)],
% 3.30/3.55                ['79', '80', '81', '82', '83', '84', '85', '86', '87', '88', 
% 3.30/3.55                 '89', '90', '91'])).
% 3.30/3.55  thf('93', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.55         ((zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55           X2 @ sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (v2_struct_0 @ sk_C))),
% 3.30/3.55      inference('sup-', [status(thm)], ['75', '92'])).
% 3.30/3.55  thf('94', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         ((v2_struct_0 @ sk_C)
% 3.30/3.55          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             X1 @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['74', '93'])).
% 3.30/3.55  thf('95', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('96', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         ((v2_struct_0 @ sk_C)
% 3.30/3.55          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             X1 @ sk_A))),
% 3.30/3.55      inference('demod', [status(thm)], ['94', '95'])).
% 3.30/3.55  thf('97', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.30/3.55         ((zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 3.30/3.55          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             X1 @ sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | (v2_struct_0 @ sk_C))),
% 3.30/3.55      inference('sup-', [status(thm)], ['73', '96'])).
% 3.30/3.55  thf('98', plain,
% 3.30/3.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.30/3.55         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 3.30/3.55          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.55  thf('99', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.30/3.55         ((v2_struct_0 @ sk_C)
% 3.30/3.55          | (r3_orders_2 @ sk_A @ sk_B @ X1)
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A)
% 3.30/3.55          | (zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             X0 @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['97', '98'])).
% 3.30/3.55  thf('100', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         ((zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55           X0 @ sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ sk_B @ X1)
% 3.30/3.55          | (v2_struct_0 @ sk_C))),
% 3.30/3.55      inference('eq_fact', [status(thm)], ['99'])).
% 3.30/3.55  thf('101', plain,
% 3.30/3.55      (![X43 : $i]:
% 3.30/3.55         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X43) @ sk_A @ sk_A)
% 3.30/3.55          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('102', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         ((v2_struct_0 @ sk_C)
% 3.30/3.55          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             X1 @ sk_A)
% 3.30/3.55          | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['100', '101'])).
% 3.30/3.55  thf('103', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 3.30/3.55          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.55  thf('104', plain,
% 3.30/3.55      (((v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 3.30/3.55        | (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | ~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B))),
% 3.30/3.55      inference('sup-', [status(thm)], ['102', '103'])).
% 3.30/3.55  thf('105', plain,
% 3.30/3.55      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['72', '104'])).
% 3.30/3.55  thf('106', plain,
% 3.30/3.55      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (m1_subset_1 @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.55           (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['51', '62'])).
% 3.30/3.55  thf('107', plain,
% 3.30/3.55      (![X33 : $i]: ((l1_orders_2 @ X33) | ~ (l1_waybel_9 @ X33))),
% 3.30/3.55      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 3.30/3.55  thf('108', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf(redefinition_r3_orders_2, axiom,
% 3.30/3.55    (![A:$i,B:$i,C:$i]:
% 3.30/3.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.30/3.55         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 3.30/3.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 3.30/3.55       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 3.30/3.55  thf('109', plain,
% 3.30/3.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.30/3.55         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 3.30/3.55          | ~ (l1_orders_2 @ X8)
% 3.30/3.55          | ~ (v3_orders_2 @ X8)
% 3.30/3.55          | (v2_struct_0 @ X8)
% 3.30/3.55          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 3.30/3.55          | (r1_orders_2 @ X8 @ X7 @ X9)
% 3.30/3.55          | ~ (r3_orders_2 @ X8 @ X7 @ X9))),
% 3.30/3.55      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 3.30/3.55  thf('110', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | ~ (v3_orders_2 @ sk_A)
% 3.30/3.55          | ~ (l1_orders_2 @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['108', '109'])).
% 3.30/3.55  thf('111', plain, ((v3_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('112', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | ~ (l1_orders_2 @ sk_A))),
% 3.30/3.55      inference('demod', [status(thm)], ['110', '111'])).
% 3.30/3.55  thf('113', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (l1_waybel_9 @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 3.30/3.55      inference('sup-', [status(thm)], ['107', '112'])).
% 3.30/3.55  thf('114', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('115', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((v2_struct_0 @ sk_A)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 3.30/3.55      inference('demod', [status(thm)], ['113', '114'])).
% 3.30/3.55  thf('116', plain,
% 3.30/3.55      (((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55         sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['106', '115'])).
% 3.30/3.55  thf('117', plain,
% 3.30/3.55      (((v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['105', '116'])).
% 3.30/3.55  thf('118', plain,
% 3.30/3.55      (((r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['117'])).
% 3.30/3.55  thf('119', plain,
% 3.30/3.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.30/3.55         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 3.30/3.55          | ~ (r1_orders_2 @ X14 @ X13 @ X11))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_6])).
% 3.30/3.55  thf('120', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B @ sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | (zip_tseitin_0 @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.55             X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['118', '119'])).
% 3.30/3.55  thf('121', plain,
% 3.30/3.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.30/3.55         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 3.30/3.55          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.55  thf('122', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((v2_struct_0 @ sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 3.30/3.55          | (zip_tseitin_1 @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.55             X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['120', '121'])).
% 3.30/3.55  thf('123', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 3.30/3.55          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.55  thf('124', plain,
% 3.30/3.55      (((v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | ~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B))),
% 3.30/3.55      inference('sup-', [status(thm)], ['122', '123'])).
% 3.30/3.55  thf('125', plain,
% 3.30/3.55      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55           sk_B)
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['124'])).
% 3.30/3.55  thf('126', plain,
% 3.30/3.55      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['71', '125'])).
% 3.30/3.55  thf('127', plain,
% 3.30/3.55      (((v2_struct_0 @ sk_A)
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('simplify', [status(thm)], ['126'])).
% 3.30/3.55  thf('128', plain,
% 3.30/3.55      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55         (u1_waybel_0 @ sk_A @ sk_C))
% 3.30/3.55         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['41', '42'])).
% 3.30/3.55  thf('129', plain,
% 3.30/3.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.30/3.55         ((v2_struct_0 @ X38)
% 3.30/3.55          | ~ (v4_orders_2 @ X38)
% 3.30/3.55          | ~ (v7_waybel_0 @ X38)
% 3.30/3.55          | ~ (l1_waybel_0 @ X38 @ X39)
% 3.30/3.55          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 3.30/3.55          | ~ (r2_lattice3 @ X39 @ 
% 3.30/3.55               (k2_relset_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X39) @ 
% 3.30/3.55                (u1_waybel_0 @ X39 @ X38)) @ 
% 3.30/3.55               X41)
% 3.30/3.55          | (r3_orders_2 @ X39 @ X40 @ X41)
% 3.30/3.55          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 3.30/3.55          | ((X42) != (X40))
% 3.30/3.55          | ~ (r3_waybel_9 @ X39 @ X38 @ X42)
% 3.30/3.55          | ~ (v5_pre_topc @ (k4_waybel_1 @ X39 @ (sk_E_1 @ X39)) @ X39 @ X39)
% 3.30/3.55          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X39))
% 3.30/3.55          | ~ (l1_waybel_9 @ X39)
% 3.30/3.55          | ~ (v1_compts_1 @ X39)
% 3.30/3.55          | ~ (v2_lattice3 @ X39)
% 3.30/3.55          | ~ (v1_lattice3 @ X39)
% 3.30/3.55          | ~ (v5_orders_2 @ X39)
% 3.30/3.55          | ~ (v4_orders_2 @ X39)
% 3.30/3.55          | ~ (v3_orders_2 @ X39)
% 3.30/3.55          | ~ (v8_pre_topc @ X39)
% 3.30/3.55          | ~ (v2_pre_topc @ X39))),
% 3.30/3.55      inference('cnf', [status(esa)], [l49_waybel_9])).
% 3.30/3.55  thf('130', plain,
% 3.30/3.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.30/3.55         (~ (v2_pre_topc @ X39)
% 3.30/3.55          | ~ (v8_pre_topc @ X39)
% 3.30/3.55          | ~ (v3_orders_2 @ X39)
% 3.30/3.55          | ~ (v4_orders_2 @ X39)
% 3.30/3.55          | ~ (v5_orders_2 @ X39)
% 3.30/3.55          | ~ (v1_lattice3 @ X39)
% 3.30/3.55          | ~ (v2_lattice3 @ X39)
% 3.30/3.55          | ~ (v1_compts_1 @ X39)
% 3.30/3.55          | ~ (l1_waybel_9 @ X39)
% 3.30/3.55          | ~ (v5_pre_topc @ (k4_waybel_1 @ X39 @ (sk_E_1 @ X39)) @ X39 @ X39)
% 3.30/3.55          | ~ (r3_waybel_9 @ X39 @ X38 @ X40)
% 3.30/3.55          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 3.30/3.55          | (r3_orders_2 @ X39 @ X40 @ X41)
% 3.30/3.55          | ~ (r2_lattice3 @ X39 @ 
% 3.30/3.55               (k2_relset_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X39) @ 
% 3.30/3.55                (u1_waybel_0 @ X39 @ X38)) @ 
% 3.30/3.55               X41)
% 3.30/3.55          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 3.30/3.55          | ~ (l1_waybel_0 @ X38 @ X39)
% 3.30/3.55          | ~ (v7_waybel_0 @ X38)
% 3.30/3.55          | ~ (v4_orders_2 @ X38)
% 3.30/3.55          | (v2_struct_0 @ X38))),
% 3.30/3.55      inference('simplify', [status(thm)], ['129'])).
% 3.30/3.55  thf('131', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             X0)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | ~ (v4_orders_2 @ sk_C)
% 3.30/3.55          | ~ (v7_waybel_0 @ sk_C)
% 3.30/3.55          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 3.30/3.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 3.30/3.55          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 3.30/3.55               sk_A)
% 3.30/3.55          | ~ (l1_waybel_9 @ sk_A)
% 3.30/3.55          | ~ (v1_compts_1 @ sk_A)
% 3.30/3.55          | ~ (v2_lattice3 @ sk_A)
% 3.30/3.55          | ~ (v1_lattice3 @ sk_A)
% 3.30/3.55          | ~ (v5_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v4_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v3_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v8_pre_topc @ sk_A)
% 3.30/3.55          | ~ (v2_pre_topc @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['128', '130'])).
% 3.30/3.55  thf('132', plain, ((v4_orders_2 @ sk_C)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('133', plain, ((v7_waybel_0 @ sk_C)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('134', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('135', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('136', plain, ((v1_compts_1 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('137', plain, ((v2_lattice3 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('138', plain, ((v1_lattice3 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('139', plain, ((v5_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('140', plain, ((v4_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('141', plain, ((v3_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('142', plain, ((v8_pre_topc @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('144', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             X0)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 3.30/3.55          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 3.30/3.55               sk_A))),
% 3.30/3.55      inference('demod', [status(thm)],
% 3.30/3.55                ['131', '132', '133', '134', '135', '136', '137', '138', 
% 3.30/3.55                 '139', '140', '141', '142', '143'])).
% 3.30/3.55  thf('145', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         ((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X0 @ X1)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | ~ (r2_lattice3 @ sk_A @ 
% 3.30/3.55               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X1))),
% 3.30/3.55      inference('sup-', [status(thm)], ['127', '144'])).
% 3.30/3.55  thf('146', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             X1)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X0 @ X1)
% 3.30/3.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('simplify', [status(thm)], ['145'])).
% 3.30/3.55  thf('147', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 3.30/3.55          | ~ (m1_subset_1 @ 
% 3.30/3.55               (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.55               (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X0 @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['70', '146'])).
% 3.30/3.55  thf('148', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X0 @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55          | ~ (m1_subset_1 @ 
% 3.30/3.55               (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.55               (u1_struct_0 @ sk_A))
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['147'])).
% 3.30/3.55  thf('149', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B @ sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X0 @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['63', '148'])).
% 3.30/3.55  thf('150', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ X0 @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['149'])).
% 3.30/3.55  thf('151', plain,
% 3.30/3.55      (((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55         sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['50', '150'])).
% 3.30/3.55  thf('152', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('153', plain,
% 3.30/3.55      (((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55         sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A)))),
% 3.30/3.55      inference('demod', [status(thm)], ['151', '152'])).
% 3.30/3.55  thf('154', plain,
% 3.30/3.55      (((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55         sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['106', '115'])).
% 3.30/3.55  thf('155', plain,
% 3.30/3.55      (((v2_struct_0 @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['153', '154'])).
% 3.30/3.55  thf('156', plain,
% 3.30/3.55      (((r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['155'])).
% 3.30/3.55  thf('157', plain,
% 3.30/3.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.30/3.55         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 3.30/3.55          | ~ (r1_orders_2 @ X14 @ X13 @ X11))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_6])).
% 3.30/3.55  thf('158', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((v2_struct_0 @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B @ sk_A)
% 3.30/3.55          | (zip_tseitin_0 @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.55             X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['156', '157'])).
% 3.30/3.55  thf('159', plain,
% 3.30/3.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.30/3.55         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 3.30/3.55          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.55  thf('160', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (v2_struct_0 @ sk_A)
% 3.30/3.55          | (zip_tseitin_1 @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.55             X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['158', '159'])).
% 3.30/3.55  thf('161', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 3.30/3.55          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.55  thf('162', plain,
% 3.30/3.55      (((v2_struct_0 @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | ~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B))),
% 3.30/3.55      inference('sup-', [status(thm)], ['160', '161'])).
% 3.30/3.55  thf('163', plain,
% 3.30/3.55      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55           sk_B)
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['162'])).
% 3.30/3.55  thf('164', plain,
% 3.30/3.55      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['49', '163'])).
% 3.30/3.55  thf('165', plain,
% 3.30/3.55      (((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55         sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('simplify', [status(thm)], ['164'])).
% 3.30/3.55  thf('166', plain,
% 3.30/3.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.30/3.55         (((X21) = (k1_yellow_0 @ X19 @ X20))
% 3.30/3.55          | ~ (zip_tseitin_2 @ X20 @ X21 @ X19))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.30/3.55  thf('167', plain,
% 3.30/3.55      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 3.30/3.55      inference('sup-', [status(thm)], ['165', '166'])).
% 3.30/3.55  thf('168', plain,
% 3.30/3.55      (![X43 : $i]:
% 3.30/3.55         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X43) @ sk_A @ sk_A)
% 3.30/3.55          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('169', plain,
% 3.30/3.55      ((((sk_B)
% 3.30/3.55          = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E @ sk_A)) @ sk_A @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['167', '168'])).
% 3.30/3.55  thf('170', plain,
% 3.30/3.55      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.30/3.55         ((v2_struct_0 @ X34)
% 3.30/3.55          | ~ (v4_orders_2 @ X34)
% 3.30/3.55          | ~ (v7_waybel_0 @ X34)
% 3.30/3.55          | ~ (l1_waybel_0 @ X34 @ X35)
% 3.30/3.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 3.30/3.55          | (r2_lattice3 @ X35 @ 
% 3.30/3.55             (k2_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35) @ 
% 3.30/3.55              (u1_waybel_0 @ X35 @ X34)) @ 
% 3.30/3.55             X36)
% 3.30/3.55          | ((X37) != (X36))
% 3.30/3.55          | ~ (r3_waybel_9 @ X35 @ X34 @ X37)
% 3.30/3.55          | ~ (v10_waybel_0 @ X34 @ X35)
% 3.30/3.55          | ~ (v5_pre_topc @ (k4_waybel_1 @ X35 @ (sk_E @ X35)) @ X35 @ X35)
% 3.30/3.55          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 3.30/3.55          | ~ (l1_waybel_9 @ X35)
% 3.30/3.55          | ~ (v1_compts_1 @ X35)
% 3.30/3.55          | ~ (v2_lattice3 @ X35)
% 3.30/3.55          | ~ (v1_lattice3 @ X35)
% 3.30/3.55          | ~ (v5_orders_2 @ X35)
% 3.30/3.55          | ~ (v4_orders_2 @ X35)
% 3.30/3.55          | ~ (v3_orders_2 @ X35)
% 3.30/3.55          | ~ (v8_pre_topc @ X35)
% 3.30/3.55          | ~ (v2_pre_topc @ X35))),
% 3.30/3.55      inference('cnf', [status(esa)], [l48_waybel_9])).
% 3.30/3.55  thf('171', plain,
% 3.30/3.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.30/3.55         (~ (v2_pre_topc @ X35)
% 3.30/3.55          | ~ (v8_pre_topc @ X35)
% 3.30/3.55          | ~ (v3_orders_2 @ X35)
% 3.30/3.55          | ~ (v4_orders_2 @ X35)
% 3.30/3.55          | ~ (v5_orders_2 @ X35)
% 3.30/3.55          | ~ (v1_lattice3 @ X35)
% 3.30/3.55          | ~ (v2_lattice3 @ X35)
% 3.30/3.55          | ~ (v1_compts_1 @ X35)
% 3.30/3.55          | ~ (l1_waybel_9 @ X35)
% 3.30/3.55          | ~ (v5_pre_topc @ (k4_waybel_1 @ X35 @ (sk_E @ X35)) @ X35 @ X35)
% 3.30/3.55          | ~ (v10_waybel_0 @ X34 @ X35)
% 3.30/3.55          | ~ (r3_waybel_9 @ X35 @ X34 @ X36)
% 3.30/3.55          | (r2_lattice3 @ X35 @ 
% 3.30/3.55             (k2_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35) @ 
% 3.30/3.55              (u1_waybel_0 @ X35 @ X34)) @ 
% 3.30/3.55             X36)
% 3.30/3.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 3.30/3.55          | ~ (l1_waybel_0 @ X34 @ X35)
% 3.30/3.55          | ~ (v7_waybel_0 @ X34)
% 3.30/3.55          | ~ (v4_orders_2 @ X34)
% 3.30/3.55          | (v2_struct_0 @ X34))),
% 3.30/3.55      inference('simplify', [status(thm)], ['170'])).
% 3.30/3.55  thf('172', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         ((v2_struct_0 @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | ((sk_B)
% 3.30/3.55              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.55                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55          | (v2_struct_0 @ X0)
% 3.30/3.55          | ~ (v4_orders_2 @ X0)
% 3.30/3.55          | ~ (v7_waybel_0 @ X0)
% 3.30/3.55          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 3.30/3.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r2_lattice3 @ sk_A @ 
% 3.30/3.55             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55              (u1_waybel_0 @ sk_A @ X0)) @ 
% 3.30/3.55             X1)
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 3.30/3.55          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 3.30/3.55          | ~ (l1_waybel_9 @ sk_A)
% 3.30/3.55          | ~ (v1_compts_1 @ sk_A)
% 3.30/3.55          | ~ (v2_lattice3 @ sk_A)
% 3.30/3.55          | ~ (v1_lattice3 @ sk_A)
% 3.30/3.55          | ~ (v5_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v4_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v3_orders_2 @ sk_A)
% 3.30/3.55          | ~ (v8_pre_topc @ sk_A)
% 3.30/3.55          | ~ (v2_pre_topc @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['169', '171'])).
% 3.30/3.55  thf('173', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('174', plain, ((v1_compts_1 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('175', plain, ((v2_lattice3 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('176', plain, ((v1_lattice3 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('177', plain, ((v5_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('178', plain, ((v4_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('179', plain, ((v3_orders_2 @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('180', plain, ((v8_pre_topc @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('181', plain, ((v2_pre_topc @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('182', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         ((v2_struct_0 @ sk_A)
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | ((sk_B)
% 3.30/3.55              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.55                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55          | (v2_struct_0 @ X0)
% 3.30/3.55          | ~ (v4_orders_2 @ X0)
% 3.30/3.55          | ~ (v7_waybel_0 @ X0)
% 3.30/3.55          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 3.30/3.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r2_lattice3 @ sk_A @ 
% 3.30/3.55             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55              (u1_waybel_0 @ sk_A @ X0)) @ 
% 3.30/3.55             X1)
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 3.30/3.55          | ~ (v10_waybel_0 @ X0 @ sk_A))),
% 3.30/3.55      inference('demod', [status(thm)],
% 3.30/3.55                ['172', '173', '174', '175', '176', '177', '178', '179', 
% 3.30/3.55                 '180', '181'])).
% 3.30/3.55  thf('183', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (v10_waybel_0 @ X0 @ sk_A)
% 3.30/3.55          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 3.30/3.55          | (r2_lattice3 @ sk_A @ 
% 3.30/3.55             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55              (u1_waybel_0 @ sk_A @ X0)) @ 
% 3.30/3.55             sk_B)
% 3.30/3.55          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 3.30/3.55          | ~ (v7_waybel_0 @ X0)
% 3.30/3.55          | ~ (v4_orders_2 @ X0)
% 3.30/3.55          | (v2_struct_0 @ X0)
% 3.30/3.55          | ((sk_B)
% 3.30/3.55              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.55                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55          | (v2_struct_0 @ sk_C)
% 3.30/3.55          | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['15', '182'])).
% 3.30/3.55  thf('184', plain,
% 3.30/3.55      (((v2_struct_0 @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | ~ (v4_orders_2 @ sk_C)
% 3.30/3.55        | ~ (v7_waybel_0 @ sk_C)
% 3.30/3.55        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 3.30/3.55        | (r2_lattice3 @ sk_A @ 
% 3.30/3.55           (k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55            (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55           sk_B)
% 3.30/3.55        | ~ (v10_waybel_0 @ sk_C @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['14', '183'])).
% 3.30/3.55  thf('185', plain, ((v4_orders_2 @ sk_C)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('186', plain, ((v7_waybel_0 @ sk_C)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('187', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('188', plain,
% 3.30/3.55      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.55         (u1_waybel_0 @ sk_A @ sk_C))
% 3.30/3.55         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['41', '42'])).
% 3.30/3.55  thf('189', plain, ((v10_waybel_0 @ sk_C @ sk_A)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('190', plain,
% 3.30/3.55      (((v2_struct_0 @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55           sk_B))),
% 3.30/3.55      inference('demod', [status(thm)],
% 3.30/3.55                ['184', '185', '186', '187', '188', '189'])).
% 3.30/3.55  thf('191', plain,
% 3.30/3.55      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['190'])).
% 3.30/3.55  thf('192', plain,
% 3.30/3.55      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['190'])).
% 3.30/3.55  thf('193', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         (~ (l1_waybel_9 @ X0)
% 3.30/3.55          | ((k4_yellow_2 @ X0 @ X1) = (k1_yellow_0 @ X0 @ (k2_relat_1 @ X1)))
% 3.30/3.55          | ~ (v1_relat_1 @ X1)
% 3.30/3.55          | ~ (v1_lattice3 @ X0))),
% 3.30/3.55      inference('sup-', [status(thm)], ['8', '12'])).
% 3.30/3.55  thf('194', plain,
% 3.30/3.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.30/3.55         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 3.30/3.55          | (m1_subset_1 @ X15 @ (u1_struct_0 @ X18)))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.55  thf('195', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.55  thf('196', plain,
% 3.30/3.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.30/3.55         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 3.30/3.55          | (r2_lattice3 @ X14 @ X12 @ X11))),
% 3.30/3.55      inference('cnf', [status(esa)], [zf_stmt_6])).
% 3.30/3.55  thf('197', plain,
% 3.30/3.55      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['190'])).
% 3.30/3.55  thf('198', plain,
% 3.30/3.55      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['190'])).
% 3.30/3.55  thf('199', plain,
% 3.30/3.55      (![X0 : $i, X1 : $i]:
% 3.30/3.55         ((zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55           X0 @ sk_A)
% 3.30/3.55          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r3_orders_2 @ sk_A @ sk_B @ X1)
% 3.30/3.55          | (v2_struct_0 @ sk_C))),
% 3.30/3.55      inference('eq_fact', [status(thm)], ['99'])).
% 3.30/3.55  thf('200', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 3.30/3.55          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 3.30/3.55      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.55  thf('201', plain,
% 3.30/3.55      (((v2_struct_0 @ sk_C)
% 3.30/3.55        | (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | ~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.55             sk_B))),
% 3.30/3.55      inference('sup-', [status(thm)], ['199', '200'])).
% 3.30/3.55  thf('202', plain,
% 3.30/3.55      (((v2_struct_0 @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_C))),
% 3.30/3.55      inference('sup-', [status(thm)], ['198', '201'])).
% 3.30/3.55  thf('203', plain,
% 3.30/3.55      (((r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['202'])).
% 3.30/3.55  thf('204', plain,
% 3.30/3.55      (((r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('simplify', [status(thm)], ['190'])).
% 3.30/3.55  thf('205', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 3.30/3.55          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 3.30/3.55      inference('sup-', [status(thm)], ['52', '61'])).
% 3.30/3.55  thf('206', plain,
% 3.30/3.55      (((v2_struct_0 @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55           sk_A)
% 3.30/3.55        | (m1_subset_1 @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.55           (u1_struct_0 @ sk_A)))),
% 3.30/3.55      inference('sup-', [status(thm)], ['204', '205'])).
% 3.30/3.55  thf('207', plain,
% 3.30/3.55      (![X0 : $i]:
% 3.30/3.55         ((v2_struct_0 @ sk_A)
% 3.30/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.55          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.55          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 3.30/3.55      inference('demod', [status(thm)], ['113', '114'])).
% 3.30/3.55  thf('208', plain,
% 3.30/3.55      (((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.55         sk_A)
% 3.30/3.55        | ((sk_B)
% 3.30/3.55            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_A))),
% 3.30/3.55      inference('sup-', [status(thm)], ['206', '207'])).
% 3.30/3.55  thf('209', plain,
% 3.30/3.55      (((r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.55             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.55        | (v2_struct_0 @ sk_A)
% 3.30/3.55        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['208'])).
% 3.30/3.56  thf('210', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | (r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.56           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A)))),
% 3.30/3.56      inference('sup-', [status(thm)], ['203', '209'])).
% 3.30/3.56  thf('211', plain,
% 3.30/3.56      (((r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.56         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.56        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['210'])).
% 3.30/3.56  thf('212', plain,
% 3.30/3.56      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.30/3.56         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 3.30/3.56          | ~ (r1_orders_2 @ X14 @ X13 @ X11))),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_6])).
% 3.30/3.56  thf('213', plain,
% 3.30/3.56      (![X0 : $i]:
% 3.30/3.56         ((v2_struct_0 @ sk_A)
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | ((sk_B)
% 3.30/3.56              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.56                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             sk_B @ sk_A)
% 3.30/3.56          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | (zip_tseitin_0 @ 
% 3.30/3.56             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.56             X0 @ sk_B @ sk_A))),
% 3.30/3.56      inference('sup-', [status(thm)], ['211', '212'])).
% 3.30/3.56  thf('214', plain,
% 3.30/3.56      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.30/3.56         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 3.30/3.56          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.56  thf('215', plain,
% 3.30/3.56      (![X0 : $i]:
% 3.30/3.56         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             sk_B @ sk_A)
% 3.30/3.56          | ((sk_B)
% 3.30/3.56              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.56                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | (zip_tseitin_1 @ 
% 3.30/3.56             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.56             X0 @ sk_B @ sk_A))),
% 3.30/3.56      inference('sup-', [status(thm)], ['213', '214'])).
% 3.30/3.56  thf('216', plain,
% 3.30/3.56      (![X0 : $i]:
% 3.30/3.56         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 3.30/3.56          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.56          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 3.30/3.56      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.56  thf('217', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             sk_B))),
% 3.30/3.56      inference('sup-', [status(thm)], ['215', '216'])).
% 3.30/3.56  thf('218', plain,
% 3.30/3.56      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56           sk_B)
% 3.30/3.56        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['217'])).
% 3.30/3.56  thf('219', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.56      inference('sup-', [status(thm)], ['197', '218'])).
% 3.30/3.56  thf('220', plain,
% 3.30/3.56      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['219'])).
% 3.30/3.56  thf('221', plain,
% 3.30/3.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.30/3.56         (((X21) = (k1_yellow_0 @ X19 @ X20))
% 3.30/3.56          | ~ (zip_tseitin_2 @ X20 @ X21 @ X19))),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.30/3.56  thf('222', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 3.30/3.56      inference('sup-', [status(thm)], ['220', '221'])).
% 3.30/3.56  thf('223', plain,
% 3.30/3.56      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['222'])).
% 3.30/3.56  thf('224', plain,
% 3.30/3.56      (![X43 : $i]:
% 3.30/3.56         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X43) @ sk_A @ sk_A)
% 3.30/3.56          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.56  thf('225', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 3.30/3.56      inference('sup-', [status(thm)], ['223', '224'])).
% 3.30/3.56  thf('226', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i]:
% 3.30/3.56         (~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             X0)
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 3.30/3.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 3.30/3.56          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 3.30/3.56               sk_A))),
% 3.30/3.56      inference('demod', [status(thm)],
% 3.30/3.56                ['131', '132', '133', '134', '135', '136', '137', '138', 
% 3.30/3.56                 '139', '140', '141', '142', '143'])).
% 3.30/3.56  thf('227', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i]:
% 3.30/3.56         (((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 3.30/3.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | (r3_orders_2 @ sk_A @ X0 @ X1)
% 3.30/3.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | ~ (r2_lattice3 @ sk_A @ 
% 3.30/3.56               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X1))),
% 3.30/3.56      inference('sup-', [status(thm)], ['225', '226'])).
% 3.30/3.56  thf('228', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i]:
% 3.30/3.56         (~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             X1)
% 3.30/3.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | (r3_orders_2 @ sk_A @ X0 @ X1)
% 3.30/3.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | ((sk_B)
% 3.30/3.56              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.56                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 3.30/3.56      inference('simplify', [status(thm)], ['227'])).
% 3.30/3.56  thf('229', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.56         ((zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56           X2 @ sk_A)
% 3.30/3.56          | ((sk_B)
% 3.30/3.56              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.56                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 3.30/3.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | (r3_orders_2 @ sk_A @ X1 @ X0)
% 3.30/3.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.56      inference('sup-', [status(thm)], ['196', '228'])).
% 3.30/3.56  thf('230', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i]:
% 3.30/3.56         (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | ((sk_B)
% 3.30/3.56              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.56                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             X1 @ sk_A))),
% 3.30/3.56      inference('sup-', [status(thm)], ['195', '229'])).
% 3.30/3.56  thf('231', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.56  thf('232', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i]:
% 3.30/3.56         ((r3_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | ((sk_B)
% 3.30/3.56              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.56                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             X1 @ sk_A))),
% 3.30/3.56      inference('demod', [status(thm)], ['230', '231'])).
% 3.30/3.56  thf('233', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.30/3.56         ((zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 3.30/3.56          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             X1 @ sk_A)
% 3.30/3.56          | ((sk_B)
% 3.30/3.56              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.56                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 3.30/3.56      inference('sup-', [status(thm)], ['194', '232'])).
% 3.30/3.56  thf('234', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.30/3.56         (((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56          | ~ (v1_lattice3 @ sk_A)
% 3.30/3.56          | ~ (v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))
% 3.30/3.56          | ~ (l1_waybel_9 @ sk_A)
% 3.30/3.56          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             X1 @ sk_A)
% 3.30/3.56          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A))),
% 3.30/3.56      inference('sup+', [status(thm)], ['193', '233'])).
% 3.30/3.56  thf('235', plain, ((v1_lattice3 @ sk_A)),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.56  thf('236', plain,
% 3.30/3.56      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 3.30/3.56        (k1_zfmisc_1 @ 
% 3.30/3.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.30/3.56      inference('demod', [status(thm)], ['35', '40'])).
% 3.30/3.56  thf(cc1_relset_1, axiom,
% 3.30/3.56    (![A:$i,B:$i,C:$i]:
% 3.30/3.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.30/3.56       ( v1_relat_1 @ C ) ))).
% 3.30/3.56  thf('237', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.56         ((v1_relat_1 @ X0)
% 3.30/3.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 3.30/3.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.30/3.56  thf('238', plain, ((v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))),
% 3.30/3.56      inference('sup-', [status(thm)], ['236', '237'])).
% 3.30/3.56  thf('239', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.56  thf('240', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.30/3.56         (((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             X1 @ sk_A)
% 3.30/3.56          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A))),
% 3.30/3.56      inference('demod', [status(thm)], ['234', '235', '238', '239'])).
% 3.30/3.56  thf('241', plain,
% 3.30/3.56      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.30/3.56         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 3.30/3.56          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.56  thf('242', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.30/3.56         ((zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A)
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | (r3_orders_2 @ sk_A @ sk_B @ X1)
% 3.30/3.56          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56          | (zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             X0 @ sk_A))),
% 3.30/3.56      inference('sup-', [status(thm)], ['240', '241'])).
% 3.30/3.56  thf('243', plain,
% 3.30/3.56      (![X0 : $i, X1 : $i]:
% 3.30/3.56         ((zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56           X0 @ sk_A)
% 3.30/3.56          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56          | (r3_orders_2 @ sk_A @ sk_B @ X1)
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | (v2_struct_0 @ sk_C))),
% 3.30/3.56      inference('eq_fact', [status(thm)], ['242'])).
% 3.30/3.56  thf('244', plain,
% 3.30/3.56      (![X0 : $i]:
% 3.30/3.56         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 3.30/3.56          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.56          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 3.30/3.56      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.56  thf('245', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.56           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             sk_B))),
% 3.30/3.56      inference('sup-', [status(thm)], ['243', '244'])).
% 3.30/3.56  thf('246', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.56           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C))),
% 3.30/3.56      inference('sup-', [status(thm)], ['192', '245'])).
% 3.30/3.56  thf('247', plain,
% 3.30/3.56      (((r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.56         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['246'])).
% 3.30/3.56  thf('248', plain,
% 3.30/3.56      (((r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.56         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.56        | ~ (r3_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.56             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['208'])).
% 3.30/3.56  thf('249', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | (r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.56           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A)))),
% 3.30/3.56      inference('sup-', [status(thm)], ['247', '248'])).
% 3.30/3.56  thf('250', plain,
% 3.30/3.56      (((r1_orders_2 @ sk_A @ sk_B @ 
% 3.30/3.56         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A))
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['249'])).
% 3.30/3.56  thf('251', plain,
% 3.30/3.56      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.30/3.56         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 3.30/3.56          | ~ (r1_orders_2 @ X14 @ X13 @ X11))),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_6])).
% 3.30/3.56  thf('252', plain,
% 3.30/3.56      (![X0 : $i]:
% 3.30/3.56         ((v2_struct_0 @ sk_A)
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | ((sk_B)
% 3.30/3.56              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.56                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             sk_B @ sk_A)
% 3.30/3.56          | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56          | (zip_tseitin_0 @ 
% 3.30/3.56             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.56             X0 @ sk_B @ sk_A))),
% 3.30/3.56      inference('sup-', [status(thm)], ['250', '251'])).
% 3.30/3.56  thf('253', plain,
% 3.30/3.56      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.30/3.56         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 3.30/3.56          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.56  thf('254', plain,
% 3.30/3.56      (![X0 : $i]:
% 3.30/3.56         (((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             sk_B @ sk_A)
% 3.30/3.56          | ((sk_B)
% 3.30/3.56              = (k1_yellow_0 @ sk_A @ 
% 3.30/3.56                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56          | (v2_struct_0 @ sk_C)
% 3.30/3.56          | (v2_struct_0 @ sk_A)
% 3.30/3.56          | (zip_tseitin_1 @ 
% 3.30/3.56             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 3.30/3.56             X0 @ sk_B @ sk_A))),
% 3.30/3.56      inference('sup-', [status(thm)], ['252', '253'])).
% 3.30/3.56  thf('255', plain,
% 3.30/3.56      (![X0 : $i]:
% 3.30/3.56         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 3.30/3.56          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 3.30/3.56          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 3.30/3.56      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.56  thf('256', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56             sk_B))),
% 3.30/3.56      inference('sup-', [status(thm)], ['254', '255'])).
% 3.30/3.56  thf('257', plain,
% 3.30/3.56      ((~ (r2_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 3.30/3.56           sk_B)
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['256'])).
% 3.30/3.56  thf('258', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C))))),
% 3.30/3.56      inference('sup-', [status(thm)], ['191', '257'])).
% 3.30/3.56  thf('259', plain,
% 3.30/3.56      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 3.30/3.56           sk_A)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['258'])).
% 3.30/3.56  thf('260', plain,
% 3.30/3.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.30/3.56         (((X21) = (k1_yellow_0 @ X19 @ X20))
% 3.30/3.56          | ~ (zip_tseitin_2 @ X20 @ X21 @ X19))),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.30/3.56  thf('261', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 3.30/3.56      inference('sup-', [status(thm)], ['259', '260'])).
% 3.30/3.56  thf('262', plain,
% 3.30/3.56      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | ((sk_B)
% 3.30/3.56            = (k1_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('simplify', [status(thm)], ['261'])).
% 3.30/3.56  thf('263', plain,
% 3.30/3.56      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | ~ (v1_lattice3 @ sk_A)
% 3.30/3.56        | ~ (v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))
% 3.30/3.56        | ~ (l1_waybel_9 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C))))),
% 3.30/3.56      inference('sup+', [status(thm)], ['13', '262'])).
% 3.30/3.56  thf('264', plain, ((v1_lattice3 @ sk_A)),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.56  thf('265', plain, ((v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))),
% 3.30/3.56      inference('sup-', [status(thm)], ['236', '237'])).
% 3.30/3.56  thf('266', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.56  thf('267', plain,
% 3.30/3.56      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_C)
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C))))),
% 3.30/3.56      inference('demod', [status(thm)], ['263', '264', '265', '266'])).
% 3.30/3.56  thf('268', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_C)
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | ((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C))))),
% 3.30/3.56      inference('simplify', [status(thm)], ['267'])).
% 3.30/3.56  thf('269', plain, (~ (v2_struct_0 @ sk_C)),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.56  thf('270', plain,
% 3.30/3.56      ((((sk_B) = (k4_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('clc', [status(thm)], ['268', '269'])).
% 3.30/3.56  thf('271', plain,
% 3.30/3.56      ((((sk_B) = (k1_waybel_2 @ sk_A @ sk_C))
% 3.30/3.56        | (v2_struct_0 @ sk_A)
% 3.30/3.56        | (v2_struct_0 @ sk_A))),
% 3.30/3.56      inference('sup+', [status(thm)], ['7', '270'])).
% 3.30/3.56  thf('272', plain,
% 3.30/3.56      (((v2_struct_0 @ sk_A) | ((sk_B) = (k1_waybel_2 @ sk_A @ sk_C)))),
% 3.30/3.56      inference('simplify', [status(thm)], ['271'])).
% 3.30/3.56  thf('273', plain, (((sk_B) != (k1_waybel_2 @ sk_A @ sk_C))),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.56  thf('274', plain, ((v2_struct_0 @ sk_A)),
% 3.30/3.56      inference('simplify_reflect-', [status(thm)], ['272', '273'])).
% 3.30/3.56  thf('275', plain,
% 3.30/3.56      (![X10 : $i]:
% 3.30/3.56         (~ (v1_lattice3 @ X10) | ~ (v2_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 3.30/3.56      inference('cnf', [status(esa)], [cc1_lattice3])).
% 3.30/3.56  thf('276', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 3.30/3.56      inference('sup-', [status(thm)], ['274', '275'])).
% 3.30/3.56  thf('277', plain, ((v1_lattice3 @ sk_A)),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.56  thf('278', plain, (~ (l1_orders_2 @ sk_A)),
% 3.30/3.56      inference('demod', [status(thm)], ['276', '277'])).
% 3.30/3.56  thf('279', plain, (~ (l1_waybel_9 @ sk_A)),
% 3.30/3.56      inference('sup-', [status(thm)], ['0', '278'])).
% 3.30/3.56  thf('280', plain, ((l1_waybel_9 @ sk_A)),
% 3.30/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.56  thf('281', plain, ($false), inference('demod', [status(thm)], ['279', '280'])).
% 3.30/3.56  
% 3.30/3.56  % SZS output end Refutation
% 3.30/3.56  
% 3.30/3.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
