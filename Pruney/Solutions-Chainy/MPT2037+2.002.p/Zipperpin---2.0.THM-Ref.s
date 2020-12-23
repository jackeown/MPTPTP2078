%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qGydKHNPbL

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:35 EST 2020

% Result     : Theorem 5.51s
% Output     : Refutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :  308 (3611 expanded)
%              Number of leaves         :   63 (1111 expanded)
%              Depth                    :   86
%              Number of atoms          : 4390 (108575 expanded)
%              Number of equality atoms :  105 (1924 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k5_yellow_2_type,type,(
    k5_yellow_2: $i > $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_waybel_9_type,type,(
    k1_waybel_9: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v11_waybel_0_type,type,(
    v11_waybel_0: $i > $i > $o )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_waybel_0 @ X26 @ X27 )
      | ( ( k1_waybel_9 @ X27 @ X26 )
        = ( k5_yellow_2 @ X27 @ ( u1_waybel_0 @ X27 @ X26 ) ) )
      | ~ ( l1_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_waybel_9])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_waybel_9 @ sk_A @ sk_C )
      = ( k5_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('4',plain,(
    ! [X30: $i] :
      ( ( l1_orders_2 @ X30 )
      | ~ ( l1_waybel_9 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_waybel_9 @ sk_A @ sk_C )
      = ( k5_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(d6_yellow_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k5_yellow_2 @ A @ B )
            = ( k2_yellow_0 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('7',plain,(
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

thf('8',plain,(
    ! [X7: $i] :
      ( ~ ( v1_lattice3 @ X7 )
      | ~ ( v2_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k5_yellow_2 @ X0 @ X1 )
        = ( k2_yellow_0 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_yellow_2 @ X0 @ X1 )
        = ( k2_yellow_0 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
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

thf('16',plain,(
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
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
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
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_B )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21','22','23','24','25','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v11_waybel_0 @ sk_C @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( v7_waybel_0 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    v11_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('30',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X24 )
      | ~ ( l1_waybel_0 @ X25 @ X24 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('33',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X30: $i] :
      ( ( l1_pre_topc @ X30 )
      | ~ ( l1_waybel_9 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k2_relset_1 @ X4 @ X5 @ X3 )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['28','29','40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

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

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r1_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ D @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( r1_lattice3 @ X11 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('52',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( r1_lattice3 @ X11 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('56',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

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

thf('57',plain,(
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

thf('58',plain,(
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
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
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
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64','65','66','67','68','69','70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X2 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','76'])).

thf('78',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(eq_fact,[status(thm)],['79'])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_lattice3 @ X20 @ X23 @ X19 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 @ X19 @ X20 )
      | ( zip_tseitin_2 @ X23 @ X19 @ X20 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','87'])).

thf('89',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( r1_orders_2 @ X11 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','95'])).

thf('97',plain,
    ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k2_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('99',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('103',plain,(
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

thf('104',plain,(
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
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
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
    inference('sup-',[status(thm)],['102','104'])).

thf('106',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109','110','111','112','113','114','115','116','117'])).

thf('119',plain,(
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
    inference('sup-',[status(thm)],['101','118'])).

thf('120',plain,(
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
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
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
    inference('sup-',[status(thm)],['50','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','124'])).

thf('126',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('130',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','130'])).

thf('132',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( r1_orders_2 @ X11 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('138',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['46','139'])).

thf('141',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k2_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('143',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
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

thf('150',plain,(
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
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
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
    inference('sup-',[status(thm)],['148','150'])).

thf('152',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
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
    inference(demod,[status(thm)],['151','152','153','154','155','156','157','158','159','160'])).

thf('162',plain,(
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
    inference('sup-',[status(thm)],['12','161'])).

thf('163',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ~ ( v7_waybel_0 @ sk_C )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ~ ( v11_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['11','162'])).

thf('164',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    = ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('168',plain,(
    v11_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['163','164','165','166','167','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('173',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('174',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k2_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('179',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( r1_lattice3 @ X11 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('182',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('183',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('185',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( r1_orders_2 @ X11 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['182','192'])).

thf('194',plain,
    ( ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k2_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('196',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109','110','111','112','113','114','115','116','117'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X2 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ X1 )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['181','203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','204'])).

thf('206',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['179','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('213',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['172','213'])).

thf('215',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( r1_orders_2 @ X11 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('221',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['171','222'])).

thf('224',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) )
    | ( zip_tseitin_2 @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k2_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('228',plain,
    ( sk_B
    = ( k2_yellow_0 @ sk_A @ ( k2_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( sk_B
      = ( k5_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','228'])).

thf('230',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('231',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('232',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('233',plain,(
    v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( sk_B
    = ( k5_yellow_2 @ sk_A @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['229','230','233','234'])).

thf('236',plain,
    ( ( sk_B
      = ( k1_waybel_9 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','235'])).

thf('237',plain,(
    sk_B
 != ( k1_waybel_9 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['236','237'])).

thf('239',plain,(
    ! [X7: $i] :
      ( ~ ( v1_lattice3 @ X7 )
      | ~ ( v2_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('240',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('242',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    $false ),
    inference(demod,[status(thm)],['240','241','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qGydKHNPbL
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:32:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 5.51/5.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.51/5.78  % Solved by: fo/fo7.sh
% 5.51/5.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.51/5.78  % done 2159 iterations in 5.329s
% 5.51/5.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.51/5.78  % SZS output start Refutation
% 5.51/5.78  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 5.51/5.78  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 5.51/5.78  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 5.51/5.78  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.51/5.78  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 5.51/5.78  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 5.51/5.78  thf(k5_yellow_2_type, type, k5_yellow_2: $i > $i > $i).
% 5.51/5.78  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 5.51/5.78  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 5.51/5.78  thf(sk_C_type, type, sk_C: $i).
% 5.51/5.78  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 5.51/5.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 5.51/5.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 5.51/5.78  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 5.51/5.78  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 5.51/5.78  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 5.51/5.78  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 5.51/5.78  thf(sk_E_type, type, sk_E: $i > $i).
% 5.51/5.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.51/5.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.51/5.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.51/5.78  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 5.51/5.78  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 5.51/5.78  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 5.51/5.78  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 5.51/5.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.51/5.78  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.51/5.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.51/5.78  thf(k1_waybel_9_type, type, k1_waybel_9: $i > $i > $i).
% 5.51/5.78  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 5.51/5.78  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 5.51/5.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.51/5.78  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 5.51/5.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.51/5.78  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 5.51/5.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.51/5.78  thf(v11_waybel_0_type, type, v11_waybel_0: $i > $i > $o).
% 5.51/5.78  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 5.51/5.78  thf(sk_B_type, type, sk_B: $i).
% 5.51/5.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.51/5.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.51/5.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.51/5.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.51/5.78  thf(sk_A_type, type, sk_A: $i).
% 5.51/5.78  thf(t36_waybel_9, conjecture,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 5.51/5.78         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 5.51/5.78         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78           ( ![C:$i]:
% 5.51/5.78             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 5.51/5.78                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 5.51/5.78               ( ( ( ![D:$i]:
% 5.51/5.78                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78                       ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 5.51/5.78                   ( v11_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 5.51/5.78                 ( ( B ) = ( k1_waybel_9 @ A @ C ) ) ) ) ) ) ) ))).
% 5.51/5.78  thf(zf_stmt_0, negated_conjecture,
% 5.51/5.78    (~( ![A:$i]:
% 5.51/5.78        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 5.51/5.78            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 5.51/5.78            ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 5.51/5.78          ( ![B:$i]:
% 5.51/5.78            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78              ( ![C:$i]:
% 5.51/5.78                ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 5.51/5.78                    ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 5.51/5.78                  ( ( ( ![D:$i]:
% 5.51/5.78                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78                          ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 5.51/5.78                      ( v11_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 5.51/5.78                    ( ( B ) = ( k1_waybel_9 @ A @ C ) ) ) ) ) ) ) ) )),
% 5.51/5.78    inference('cnf.neg', [status(esa)], [t36_waybel_9])).
% 5.51/5.78  thf('0', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf(d2_waybel_9, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( l1_waybel_0 @ B @ A ) =>
% 5.51/5.78           ( ( k1_waybel_9 @ A @ B ) =
% 5.51/5.78             ( k5_yellow_2 @ A @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 5.51/5.78  thf('1', plain,
% 5.51/5.78      (![X26 : $i, X27 : $i]:
% 5.51/5.78         (~ (l1_waybel_0 @ X26 @ X27)
% 5.51/5.78          | ((k1_waybel_9 @ X27 @ X26)
% 5.51/5.78              = (k5_yellow_2 @ X27 @ (u1_waybel_0 @ X27 @ X26)))
% 5.51/5.78          | ~ (l1_orders_2 @ X27)
% 5.51/5.78          | (v2_struct_0 @ X27))),
% 5.51/5.78      inference('cnf', [status(esa)], [d2_waybel_9])).
% 5.51/5.78  thf('2', plain,
% 5.51/5.78      (((v2_struct_0 @ sk_A)
% 5.51/5.78        | ~ (l1_orders_2 @ sk_A)
% 5.51/5.78        | ((k1_waybel_9 @ sk_A @ sk_C)
% 5.51/5.78            = (k5_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['0', '1'])).
% 5.51/5.78  thf('3', plain, ((l1_waybel_9 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf(dt_l1_waybel_9, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 5.51/5.78  thf('4', plain, (![X30 : $i]: ((l1_orders_2 @ X30) | ~ (l1_waybel_9 @ X30))),
% 5.51/5.78      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 5.51/5.78  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 5.51/5.78      inference('sup-', [status(thm)], ['3', '4'])).
% 5.51/5.78  thf('6', plain,
% 5.51/5.78      (((v2_struct_0 @ sk_A)
% 5.51/5.78        | ((k1_waybel_9 @ sk_A @ sk_C)
% 5.51/5.78            = (k5_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C))))),
% 5.51/5.78      inference('demod', [status(thm)], ['2', '5'])).
% 5.51/5.78  thf(d6_yellow_2, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( v1_relat_1 @ B ) =>
% 5.51/5.78           ( ( k5_yellow_2 @ A @ B ) = ( k2_yellow_0 @ A @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 5.51/5.78  thf('7', plain,
% 5.51/5.78      (![X28 : $i, X29 : $i]:
% 5.51/5.78         (~ (v1_relat_1 @ X28)
% 5.51/5.78          | ((k5_yellow_2 @ X29 @ X28)
% 5.51/5.78              = (k2_yellow_0 @ X29 @ (k2_relat_1 @ X28)))
% 5.51/5.78          | ~ (l1_orders_2 @ X29)
% 5.51/5.78          | (v2_struct_0 @ X29))),
% 5.51/5.78      inference('cnf', [status(esa)], [d6_yellow_2])).
% 5.51/5.78  thf(cc1_lattice3, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( l1_orders_2 @ A ) =>
% 5.51/5.78       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 5.51/5.78  thf('8', plain,
% 5.51/5.78      (![X7 : $i]:
% 5.51/5.78         (~ (v1_lattice3 @ X7) | ~ (v2_struct_0 @ X7) | ~ (l1_orders_2 @ X7))),
% 5.51/5.78      inference('cnf', [status(esa)], [cc1_lattice3])).
% 5.51/5.78  thf('9', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (~ (l1_orders_2 @ X0)
% 5.51/5.78          | ((k5_yellow_2 @ X0 @ X1) = (k2_yellow_0 @ X0 @ (k2_relat_1 @ X1)))
% 5.51/5.78          | ~ (v1_relat_1 @ X1)
% 5.51/5.78          | ~ (l1_orders_2 @ X0)
% 5.51/5.78          | ~ (v1_lattice3 @ X0))),
% 5.51/5.78      inference('sup-', [status(thm)], ['7', '8'])).
% 5.51/5.78  thf('10', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (~ (v1_lattice3 @ X0)
% 5.51/5.78          | ~ (v1_relat_1 @ X1)
% 5.51/5.78          | ((k5_yellow_2 @ X0 @ X1) = (k2_yellow_0 @ X0 @ (k2_relat_1 @ X1)))
% 5.51/5.78          | ~ (l1_orders_2 @ X0))),
% 5.51/5.78      inference('simplify', [status(thm)], ['9'])).
% 5.51/5.78  thf('11', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('13', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('14', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf(l51_waybel_9, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 5.51/5.78         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 5.51/5.78         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 5.51/5.78             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 5.51/5.78           ( ![C:$i]:
% 5.51/5.78             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78               ( ![D:$i]:
% 5.51/5.78                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78                   ( ( ( ( C ) = ( D ) ) & 
% 5.51/5.78                       ( ![E:$i]:
% 5.51/5.78                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 5.51/5.78                       ( v11_waybel_0 @ B @ A ) & ( r3_waybel_9 @ A @ B @ C ) ) =>
% 5.51/5.78                     ( r1_lattice3 @
% 5.51/5.78                       A @ 
% 5.51/5.78                       ( k2_relset_1 @
% 5.51/5.78                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 5.51/5.78                         ( u1_waybel_0 @ A @ B ) ) @ 
% 5.51/5.78                       D ) ) ) ) ) ) ) ) ))).
% 5.51/5.78  thf('15', plain,
% 5.51/5.78      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 5.51/5.78         ((v2_struct_0 @ X31)
% 5.51/5.78          | ~ (v4_orders_2 @ X31)
% 5.51/5.78          | ~ (v7_waybel_0 @ X31)
% 5.51/5.78          | ~ (l1_waybel_0 @ X31 @ X32)
% 5.51/5.78          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 5.51/5.78          | (r1_lattice3 @ X32 @ 
% 5.51/5.78             (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 5.51/5.78              (u1_waybel_0 @ X32 @ X31)) @ 
% 5.51/5.78             X33)
% 5.51/5.78          | ((X34) != (X33))
% 5.51/5.78          | ~ (r3_waybel_9 @ X32 @ X31 @ X34)
% 5.51/5.78          | ~ (v11_waybel_0 @ X31 @ X32)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ X32) @ (u1_struct_0 @ X32))
% 5.51/5.78          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 5.51/5.78          | ~ (l1_waybel_9 @ X32)
% 5.51/5.78          | ~ (v1_compts_1 @ X32)
% 5.51/5.78          | ~ (v2_lattice3 @ X32)
% 5.51/5.78          | ~ (v1_lattice3 @ X32)
% 5.51/5.78          | ~ (v5_orders_2 @ X32)
% 5.51/5.78          | ~ (v4_orders_2 @ X32)
% 5.51/5.78          | ~ (v3_orders_2 @ X32)
% 5.51/5.78          | ~ (v8_pre_topc @ X32)
% 5.51/5.78          | ~ (v2_pre_topc @ X32))),
% 5.51/5.78      inference('cnf', [status(esa)], [l51_waybel_9])).
% 5.51/5.78  thf('16', plain,
% 5.51/5.78      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.51/5.78         (~ (v2_pre_topc @ X32)
% 5.51/5.78          | ~ (v8_pre_topc @ X32)
% 5.51/5.78          | ~ (v3_orders_2 @ X32)
% 5.51/5.78          | ~ (v4_orders_2 @ X32)
% 5.51/5.78          | ~ (v5_orders_2 @ X32)
% 5.51/5.78          | ~ (v1_lattice3 @ X32)
% 5.51/5.78          | ~ (v2_lattice3 @ X32)
% 5.51/5.78          | ~ (v1_compts_1 @ X32)
% 5.51/5.78          | ~ (l1_waybel_9 @ X32)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ X32) @ (u1_struct_0 @ X32))
% 5.51/5.78          | ~ (v11_waybel_0 @ X31 @ X32)
% 5.51/5.78          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 5.51/5.78          | (r1_lattice3 @ X32 @ 
% 5.51/5.78             (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 5.51/5.78              (u1_waybel_0 @ X32 @ X31)) @ 
% 5.51/5.78             X33)
% 5.51/5.78          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 5.51/5.78          | ~ (l1_waybel_0 @ X31 @ X32)
% 5.51/5.78          | ~ (v7_waybel_0 @ X31)
% 5.51/5.78          | ~ (v4_orders_2 @ X31)
% 5.51/5.78          | (v2_struct_0 @ X31))),
% 5.51/5.78      inference('simplify', [status(thm)], ['15'])).
% 5.51/5.78  thf('17', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((v2_struct_0 @ X0)
% 5.51/5.78          | ~ (v4_orders_2 @ X0)
% 5.51/5.78          | ~ (v7_waybel_0 @ X0)
% 5.51/5.78          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 5.51/5.78          | (r1_lattice3 @ sk_A @ 
% 5.51/5.78             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78              (u1_waybel_0 @ sk_A @ X0)) @ 
% 5.51/5.78             sk_B)
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (l1_waybel_9 @ sk_A)
% 5.51/5.78          | ~ (v1_compts_1 @ sk_A)
% 5.51/5.78          | ~ (v2_lattice3 @ sk_A)
% 5.51/5.78          | ~ (v1_lattice3 @ sk_A)
% 5.51/5.78          | ~ (v5_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v4_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v3_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v8_pre_topc @ sk_A)
% 5.51/5.78          | ~ (v2_pre_topc @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['14', '16'])).
% 5.51/5.78  thf('18', plain, ((l1_waybel_9 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('19', plain, ((v1_compts_1 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('20', plain, ((v2_lattice3 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('21', plain, ((v1_lattice3 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('23', plain, ((v4_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('24', plain, ((v3_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('25', plain, ((v8_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('27', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((v2_struct_0 @ X0)
% 5.51/5.78          | ~ (v4_orders_2 @ X0)
% 5.51/5.78          | ~ (v7_waybel_0 @ X0)
% 5.51/5.78          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 5.51/5.78          | (r1_lattice3 @ sk_A @ 
% 5.51/5.78             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78              (u1_waybel_0 @ sk_A @ X0)) @ 
% 5.51/5.78             sk_B)
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('demod', [status(thm)],
% 5.51/5.78                ['17', '18', '19', '20', '21', '22', '23', '24', '25', '26'])).
% 5.51/5.78  thf('28', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | ~ (v11_waybel_0 @ sk_C @ sk_A)
% 5.51/5.78        | (r1_lattice3 @ sk_A @ 
% 5.51/5.78           (k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78            (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 5.51/5.78        | ~ (v7_waybel_0 @ sk_C)
% 5.51/5.78        | ~ (v4_orders_2 @ sk_C)
% 5.51/5.78        | (v2_struct_0 @ sk_C))),
% 5.51/5.78      inference('sup-', [status(thm)], ['13', '27'])).
% 5.51/5.78  thf('29', plain, ((v11_waybel_0 @ sk_C @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf(dt_l1_pre_topc, axiom,
% 5.51/5.78    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 5.51/5.78  thf('30', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 5.51/5.78      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.51/5.78  thf('31', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf(dt_u1_waybel_0, axiom,
% 5.51/5.78    (![A:$i,B:$i]:
% 5.51/5.78     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 5.51/5.78       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 5.51/5.78         ( v1_funct_2 @
% 5.51/5.78           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 5.51/5.78         ( m1_subset_1 @
% 5.51/5.78           ( u1_waybel_0 @ A @ B ) @ 
% 5.51/5.78           ( k1_zfmisc_1 @
% 5.51/5.78             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 5.51/5.78  thf('32', plain,
% 5.51/5.78      (![X24 : $i, X25 : $i]:
% 5.51/5.78         (~ (l1_struct_0 @ X24)
% 5.51/5.78          | ~ (l1_waybel_0 @ X25 @ X24)
% 5.51/5.78          | (m1_subset_1 @ (u1_waybel_0 @ X24 @ X25) @ 
% 5.51/5.78             (k1_zfmisc_1 @ 
% 5.51/5.78              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24)))))),
% 5.51/5.78      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 5.51/5.78  thf('33', plain,
% 5.51/5.78      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 5.51/5.78         (k1_zfmisc_1 @ 
% 5.51/5.78          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 5.51/5.78        | ~ (l1_struct_0 @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['31', '32'])).
% 5.51/5.78  thf('34', plain,
% 5.51/5.78      ((~ (l1_pre_topc @ sk_A)
% 5.51/5.78        | (m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 5.51/5.78           (k1_zfmisc_1 @ 
% 5.51/5.78            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['30', '33'])).
% 5.51/5.78  thf('35', plain, ((l1_waybel_9 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('36', plain,
% 5.51/5.78      (![X30 : $i]: ((l1_pre_topc @ X30) | ~ (l1_waybel_9 @ X30))),
% 5.51/5.78      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 5.51/5.78  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 5.51/5.78      inference('sup-', [status(thm)], ['35', '36'])).
% 5.51/5.78  thf('38', plain,
% 5.51/5.78      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 5.51/5.78        (k1_zfmisc_1 @ 
% 5.51/5.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 5.51/5.78      inference('demod', [status(thm)], ['34', '37'])).
% 5.51/5.78  thf(redefinition_k2_relset_1, axiom,
% 5.51/5.78    (![A:$i,B:$i,C:$i]:
% 5.51/5.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.51/5.78       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.51/5.78  thf('39', plain,
% 5.51/5.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.51/5.78         (((k2_relset_1 @ X4 @ X5 @ X3) = (k2_relat_1 @ X3))
% 5.51/5.78          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 5.51/5.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.51/5.78  thf('40', plain,
% 5.51/5.78      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78         (u1_waybel_0 @ sk_A @ sk_C))
% 5.51/5.78         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 5.51/5.78      inference('sup-', [status(thm)], ['38', '39'])).
% 5.51/5.78  thf('41', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('42', plain, ((v7_waybel_0 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('43', plain, ((v4_orders_2 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('44', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78        | (v2_struct_0 @ sk_C))),
% 5.51/5.78      inference('demod', [status(thm)], ['28', '29', '40', '41', '42', '43'])).
% 5.51/5.78  thf('45', plain, (~ (v2_struct_0 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('46', plain,
% 5.51/5.78      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('clc', [status(thm)], ['44', '45'])).
% 5.51/5.78  thf('47', plain,
% 5.51/5.78      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('clc', [status(thm)], ['44', '45'])).
% 5.51/5.78  thf(t31_yellow_0, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78           ( ![C:$i]:
% 5.51/5.78             ( ( ( ( r2_yellow_0 @ A @ C ) & 
% 5.51/5.78                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) =>
% 5.51/5.78                 ( ( ![D:$i]:
% 5.51/5.78                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 5.51/5.78                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 5.51/5.78                   ( r1_lattice3 @ A @ C @ B ) ) ) & 
% 5.51/5.78               ( ( ( ![D:$i]:
% 5.51/5.78                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 5.51/5.78                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 5.51/5.78                   ( r1_lattice3 @ A @ C @ B ) ) =>
% 5.51/5.78                 ( ( r2_yellow_0 @ A @ C ) & 
% 5.51/5.78                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 5.51/5.78  thf(zf_stmt_1, axiom,
% 5.51/5.78    (![D:$i,C:$i,B:$i,A:$i]:
% 5.51/5.78     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 5.51/5.78       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 5.51/5.78  thf('48', plain,
% 5.51/5.78      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.51/5.78          | (m1_subset_1 @ X12 @ (u1_struct_0 @ X15)))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.51/5.78  thf('49', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf(zf_stmt_2, axiom,
% 5.51/5.78    (![D:$i,C:$i,B:$i,A:$i]:
% 5.51/5.78     ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ D @ B ) ) =>
% 5.51/5.78       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 5.51/5.78  thf('50', plain,
% 5.51/5.78      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.51/5.78         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11) | (r1_lattice3 @ X11 @ X9 @ X8))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.51/5.78  thf('51', plain,
% 5.51/5.78      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('clc', [status(thm)], ['44', '45'])).
% 5.51/5.78  thf('52', plain,
% 5.51/5.78      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('clc', [status(thm)], ['44', '45'])).
% 5.51/5.78  thf('53', plain,
% 5.51/5.78      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.51/5.78          | (m1_subset_1 @ X12 @ (u1_struct_0 @ X15)))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.51/5.78  thf('54', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('55', plain,
% 5.51/5.78      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.51/5.78         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11) | (r1_lattice3 @ X11 @ X9 @ X8))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.51/5.78  thf('56', plain,
% 5.51/5.78      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78         (u1_waybel_0 @ sk_A @ sk_C))
% 5.51/5.78         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 5.51/5.78      inference('sup-', [status(thm)], ['38', '39'])).
% 5.51/5.78  thf(l52_waybel_9, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 5.51/5.78         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 5.51/5.78         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 5.51/5.78             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 5.51/5.78           ( ![C:$i]:
% 5.51/5.78             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78               ( ![D:$i]:
% 5.51/5.78                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78                   ( ( ( ( C ) = ( D ) ) & 
% 5.51/5.78                       ( ![E:$i]:
% 5.51/5.78                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 5.51/5.78                       ( r3_waybel_9 @ A @ B @ C ) ) =>
% 5.51/5.78                     ( ![E:$i]:
% 5.51/5.78                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78                         ( ( r1_lattice3 @
% 5.51/5.78                             A @ 
% 5.51/5.78                             ( k2_relset_1 @
% 5.51/5.78                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 5.51/5.78                               ( u1_waybel_0 @ A @ B ) ) @ 
% 5.51/5.78                             E ) =>
% 5.51/5.78                           ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 5.51/5.78  thf('57', plain,
% 5.51/5.78      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 5.51/5.78         ((v2_struct_0 @ X35)
% 5.51/5.78          | ~ (v4_orders_2 @ X35)
% 5.51/5.78          | ~ (v7_waybel_0 @ X35)
% 5.51/5.78          | ~ (l1_waybel_0 @ X35 @ X36)
% 5.51/5.78          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 5.51/5.78          | ~ (r1_lattice3 @ X36 @ 
% 5.51/5.78               (k2_relset_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36) @ 
% 5.51/5.78                (u1_waybel_0 @ X36 @ X35)) @ 
% 5.51/5.78               X38)
% 5.51/5.78          | (r1_orders_2 @ X36 @ X38 @ X37)
% 5.51/5.78          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 5.51/5.78          | ((X39) != (X37))
% 5.51/5.78          | ~ (r3_waybel_9 @ X36 @ X35 @ X39)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ X36) @ (u1_struct_0 @ X36))
% 5.51/5.78          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 5.51/5.78          | ~ (l1_waybel_9 @ X36)
% 5.51/5.78          | ~ (v1_compts_1 @ X36)
% 5.51/5.78          | ~ (v2_lattice3 @ X36)
% 5.51/5.78          | ~ (v1_lattice3 @ X36)
% 5.51/5.78          | ~ (v5_orders_2 @ X36)
% 5.51/5.78          | ~ (v4_orders_2 @ X36)
% 5.51/5.78          | ~ (v3_orders_2 @ X36)
% 5.51/5.78          | ~ (v8_pre_topc @ X36)
% 5.51/5.78          | ~ (v2_pre_topc @ X36))),
% 5.51/5.78      inference('cnf', [status(esa)], [l52_waybel_9])).
% 5.51/5.78  thf('58', plain,
% 5.51/5.78      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 5.51/5.78         (~ (v2_pre_topc @ X36)
% 5.51/5.78          | ~ (v8_pre_topc @ X36)
% 5.51/5.78          | ~ (v3_orders_2 @ X36)
% 5.51/5.78          | ~ (v4_orders_2 @ X36)
% 5.51/5.78          | ~ (v5_orders_2 @ X36)
% 5.51/5.78          | ~ (v1_lattice3 @ X36)
% 5.51/5.78          | ~ (v2_lattice3 @ X36)
% 5.51/5.78          | ~ (v1_compts_1 @ X36)
% 5.51/5.78          | ~ (l1_waybel_9 @ X36)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ X36) @ (u1_struct_0 @ X36))
% 5.51/5.78          | ~ (r3_waybel_9 @ X36 @ X35 @ X37)
% 5.51/5.78          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 5.51/5.78          | (r1_orders_2 @ X36 @ X38 @ X37)
% 5.51/5.78          | ~ (r1_lattice3 @ X36 @ 
% 5.51/5.78               (k2_relset_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36) @ 
% 5.51/5.78                (u1_waybel_0 @ X36 @ X35)) @ 
% 5.51/5.78               X38)
% 5.51/5.78          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 5.51/5.78          | ~ (l1_waybel_0 @ X35 @ X36)
% 5.51/5.78          | ~ (v7_waybel_0 @ X35)
% 5.51/5.78          | ~ (v4_orders_2 @ X35)
% 5.51/5.78          | (v2_struct_0 @ X35))),
% 5.51/5.78      inference('simplify', [status(thm)], ['57'])).
% 5.51/5.78  thf('59', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X0)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ~ (v4_orders_2 @ sk_C)
% 5.51/5.78          | ~ (v7_waybel_0 @ sk_C)
% 5.51/5.78          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (l1_waybel_9 @ sk_A)
% 5.51/5.78          | ~ (v1_compts_1 @ sk_A)
% 5.51/5.78          | ~ (v2_lattice3 @ sk_A)
% 5.51/5.78          | ~ (v1_lattice3 @ sk_A)
% 5.51/5.78          | ~ (v5_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v4_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v3_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v8_pre_topc @ sk_A)
% 5.51/5.78          | ~ (v2_pre_topc @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['56', '58'])).
% 5.51/5.78  thf('60', plain, ((v4_orders_2 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('61', plain, ((v7_waybel_0 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('62', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('63', plain, ((l1_waybel_9 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('64', plain, ((v1_compts_1 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('65', plain, ((v2_lattice3 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('66', plain, ((v1_lattice3 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('67', plain, ((v5_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('68', plain, ((v4_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('69', plain, ((v3_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('70', plain, ((v8_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('72', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X0)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('demod', [status(thm)],
% 5.51/5.78                ['59', '60', '61', '62', '63', '64', '65', '66', '67', '68', 
% 5.51/5.78                 '69', '70', '71'])).
% 5.51/5.78  thf('73', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.51/5.78         ((zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           X2 @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (v2_struct_0 @ sk_C))),
% 5.51/5.78      inference('sup-', [status(thm)], ['55', '72'])).
% 5.51/5.78  thf('74', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         ((v2_struct_0 @ sk_C)
% 5.51/5.78          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X1 @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['54', '73'])).
% 5.51/5.78  thf('75', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('76', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         ((v2_struct_0 @ sk_C)
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X1 @ sk_A))),
% 5.51/5.78      inference('demod', [status(thm)], ['74', '75'])).
% 5.51/5.78  thf('77', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 5.51/5.78          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X1 @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | (v2_struct_0 @ sk_C))),
% 5.51/5.78      inference('sup-', [status(thm)], ['53', '76'])).
% 5.51/5.78  thf('78', plain,
% 5.51/5.78      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.51/5.78          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.51/5.78  thf('79', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.51/5.78         ((v2_struct_0 @ sk_C)
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A)
% 5.51/5.78          | (zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X0 @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['77', '78'])).
% 5.51/5.78  thf('80', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           X0 @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 5.51/5.78          | (v2_struct_0 @ sk_C))),
% 5.51/5.78      inference('eq_fact', [status(thm)], ['79'])).
% 5.51/5.78  thf('81', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 5.51/5.78  thf(zf_stmt_4, axiom,
% 5.51/5.78    (![C:$i,B:$i,A:$i]:
% 5.51/5.78     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 5.51/5.78       ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & ( r2_yellow_0 @ A @ C ) ) ))).
% 5.51/5.78  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 5.51/5.78  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 5.51/5.78  thf(zf_stmt_7, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78           ( ![C:$i]:
% 5.51/5.78             ( ( ( ( r1_lattice3 @ A @ C @ B ) & 
% 5.51/5.78                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 5.51/5.78                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 5.51/5.78               ( ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & 
% 5.51/5.78                   ( r2_yellow_0 @ A @ C ) ) =>
% 5.51/5.78                 ( ( r1_lattice3 @ A @ C @ B ) & 
% 5.51/5.78                   ( ![D:$i]:
% 5.51/5.78                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 5.51/5.78                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 5.51/5.78                         ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 5.51/5.78  thf('82', plain,
% 5.51/5.78      (![X19 : $i, X20 : $i, X23 : $i]:
% 5.51/5.78         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 5.51/5.78          | ~ (r1_lattice3 @ X20 @ X23 @ X19)
% 5.51/5.78          | ~ (zip_tseitin_1 @ (sk_D @ X23 @ X19 @ X20) @ X23 @ X19 @ X20)
% 5.51/5.78          | (zip_tseitin_2 @ X23 @ X19 @ X20)
% 5.51/5.78          | ~ (l1_orders_2 @ X20)
% 5.51/5.78          | ~ (v5_orders_2 @ X20))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_7])).
% 5.51/5.78  thf('83', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         (~ (v5_orders_2 @ sk_A)
% 5.51/5.78          | ~ (l1_orders_2 @ sk_A)
% 5.51/5.78          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.51/5.78      inference('sup-', [status(thm)], ['81', '82'])).
% 5.51/5.78  thf('84', plain, ((v5_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 5.51/5.78      inference('sup-', [status(thm)], ['3', '4'])).
% 5.51/5.78  thf('86', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.51/5.78      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.51/5.78  thf('87', plain,
% 5.51/5.78      (((v2_struct_0 @ sk_C)
% 5.51/5.78        | (r1_orders_2 @ sk_A @ 
% 5.51/5.78           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B)
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['80', '86'])).
% 5.51/5.78  thf('88', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (r1_orders_2 @ sk_A @ 
% 5.51/5.78           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78        | (v2_struct_0 @ sk_C))),
% 5.51/5.78      inference('sup-', [status(thm)], ['52', '87'])).
% 5.51/5.78  thf('89', plain,
% 5.51/5.78      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.51/5.78         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 5.51/5.78          | ~ (r1_orders_2 @ X11 @ X8 @ X10))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.51/5.78  thf('90', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((v2_struct_0 @ sk_C)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_0 @ 
% 5.51/5.78             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78             X0 @ sk_B @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['88', '89'])).
% 5.51/5.78  thf('91', plain,
% 5.51/5.78      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.51/5.78          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.51/5.78  thf('92', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (zip_tseitin_1 @ 
% 5.51/5.78             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78             X0 @ sk_B @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['90', '91'])).
% 5.51/5.78  thf('93', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.51/5.78      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.51/5.78  thf('94', plain,
% 5.51/5.78      (((v2_struct_0 @ sk_C)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B)
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['92', '93'])).
% 5.51/5.78  thf('95', plain,
% 5.51/5.78      ((~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (v2_struct_0 @ sk_C))),
% 5.51/5.78      inference('simplify', [status(thm)], ['94'])).
% 5.51/5.78  thf('96', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('sup-', [status(thm)], ['51', '95'])).
% 5.51/5.78  thf('97', plain,
% 5.51/5.78      (((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78         sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('simplify', [status(thm)], ['96'])).
% 5.51/5.78  thf('98', plain,
% 5.51/5.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.51/5.78         (((X18) = (k2_yellow_0 @ X16 @ X17))
% 5.51/5.78          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.51/5.78  thf('99', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['97', '98'])).
% 5.51/5.78  thf('100', plain,
% 5.51/5.78      (![X40 : $i]:
% 5.51/5.78         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 5.51/5.78          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('101', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['99', '100'])).
% 5.51/5.78  thf('102', plain,
% 5.51/5.78      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78         (u1_waybel_0 @ sk_A @ sk_C))
% 5.51/5.78         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 5.51/5.78      inference('sup-', [status(thm)], ['38', '39'])).
% 5.51/5.78  thf('103', plain,
% 5.51/5.78      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 5.51/5.78         ((v2_struct_0 @ X35)
% 5.51/5.78          | ~ (v4_orders_2 @ X35)
% 5.51/5.78          | ~ (v7_waybel_0 @ X35)
% 5.51/5.78          | ~ (l1_waybel_0 @ X35 @ X36)
% 5.51/5.78          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 5.51/5.78          | ~ (r1_lattice3 @ X36 @ 
% 5.51/5.78               (k2_relset_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36) @ 
% 5.51/5.78                (u1_waybel_0 @ X36 @ X35)) @ 
% 5.51/5.78               X38)
% 5.51/5.78          | (r1_orders_2 @ X36 @ X38 @ X37)
% 5.51/5.78          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 5.51/5.78          | ((X39) != (X37))
% 5.51/5.78          | ~ (r3_waybel_9 @ X36 @ X35 @ X39)
% 5.51/5.78          | ~ (v5_pre_topc @ (k4_waybel_1 @ X36 @ (sk_E_1 @ X36)) @ X36 @ X36)
% 5.51/5.78          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 5.51/5.78          | ~ (l1_waybel_9 @ X36)
% 5.51/5.78          | ~ (v1_compts_1 @ X36)
% 5.51/5.78          | ~ (v2_lattice3 @ X36)
% 5.51/5.78          | ~ (v1_lattice3 @ X36)
% 5.51/5.78          | ~ (v5_orders_2 @ X36)
% 5.51/5.78          | ~ (v4_orders_2 @ X36)
% 5.51/5.78          | ~ (v3_orders_2 @ X36)
% 5.51/5.78          | ~ (v8_pre_topc @ X36)
% 5.51/5.78          | ~ (v2_pre_topc @ X36))),
% 5.51/5.78      inference('cnf', [status(esa)], [l52_waybel_9])).
% 5.51/5.78  thf('104', plain,
% 5.51/5.78      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 5.51/5.78         (~ (v2_pre_topc @ X36)
% 5.51/5.78          | ~ (v8_pre_topc @ X36)
% 5.51/5.78          | ~ (v3_orders_2 @ X36)
% 5.51/5.78          | ~ (v4_orders_2 @ X36)
% 5.51/5.78          | ~ (v5_orders_2 @ X36)
% 5.51/5.78          | ~ (v1_lattice3 @ X36)
% 5.51/5.78          | ~ (v2_lattice3 @ X36)
% 5.51/5.78          | ~ (v1_compts_1 @ X36)
% 5.51/5.78          | ~ (l1_waybel_9 @ X36)
% 5.51/5.78          | ~ (v5_pre_topc @ (k4_waybel_1 @ X36 @ (sk_E_1 @ X36)) @ X36 @ X36)
% 5.51/5.78          | ~ (r3_waybel_9 @ X36 @ X35 @ X37)
% 5.51/5.78          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 5.51/5.78          | (r1_orders_2 @ X36 @ X38 @ X37)
% 5.51/5.78          | ~ (r1_lattice3 @ X36 @ 
% 5.51/5.78               (k2_relset_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36) @ 
% 5.51/5.78                (u1_waybel_0 @ X36 @ X35)) @ 
% 5.51/5.78               X38)
% 5.51/5.78          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 5.51/5.78          | ~ (l1_waybel_0 @ X35 @ X36)
% 5.51/5.78          | ~ (v7_waybel_0 @ X35)
% 5.51/5.78          | ~ (v4_orders_2 @ X35)
% 5.51/5.78          | (v2_struct_0 @ X35))),
% 5.51/5.78      inference('simplify', [status(thm)], ['103'])).
% 5.51/5.78  thf('105', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X0)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ~ (v4_orders_2 @ sk_C)
% 5.51/5.78          | ~ (v7_waybel_0 @ sk_C)
% 5.51/5.78          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.51/5.78          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 5.51/5.78               sk_A)
% 5.51/5.78          | ~ (l1_waybel_9 @ sk_A)
% 5.51/5.78          | ~ (v1_compts_1 @ sk_A)
% 5.51/5.78          | ~ (v2_lattice3 @ sk_A)
% 5.51/5.78          | ~ (v1_lattice3 @ sk_A)
% 5.51/5.78          | ~ (v5_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v4_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v3_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v8_pre_topc @ sk_A)
% 5.51/5.78          | ~ (v2_pre_topc @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['102', '104'])).
% 5.51/5.78  thf('106', plain, ((v4_orders_2 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('107', plain, ((v7_waybel_0 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('108', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('109', plain, ((l1_waybel_9 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('110', plain, ((v1_compts_1 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('111', plain, ((v2_lattice3 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('112', plain, ((v1_lattice3 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('113', plain, ((v5_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('114', plain, ((v4_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('115', plain, ((v3_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('116', plain, ((v8_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('118', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X0)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.51/5.78          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 5.51/5.78               sk_A))),
% 5.51/5.78      inference('demod', [status(thm)],
% 5.51/5.78                ['105', '106', '107', '108', '109', '110', '111', '112', 
% 5.51/5.78                 '113', '114', '115', '116', '117'])).
% 5.51/5.78  thf('119', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         ((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X1 @ X0)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ~ (r1_lattice3 @ sk_A @ 
% 5.51/5.78               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X1))),
% 5.51/5.78      inference('sup-', [status(thm)], ['101', '118'])).
% 5.51/5.78  thf('120', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X1 @ X0)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('simplify', [status(thm)], ['119'])).
% 5.51/5.78  thf('121', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.51/5.78         ((zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           X2 @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('sup-', [status(thm)], ['50', '120'])).
% 5.51/5.78  thf('122', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X1 @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['49', '121'])).
% 5.51/5.78  thf('123', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('124', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         ((r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X1 @ sk_A))),
% 5.51/5.78      inference('demod', [status(thm)], ['122', '123'])).
% 5.51/5.78  thf('125', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 5.51/5.78          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X1 @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 5.51/5.78      inference('sup-', [status(thm)], ['48', '124'])).
% 5.51/5.78  thf('126', plain,
% 5.51/5.78      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.51/5.78          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.51/5.78  thf('127', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.51/5.78         ((r1_orders_2 @ sk_A @ X1 @ sk_B)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A)
% 5.51/5.78          | (zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X0 @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['125', '126'])).
% 5.51/5.78  thf('128', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X1 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           X0 @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X1 @ sk_B))),
% 5.51/5.78      inference('eq_fact', [status(thm)], ['127'])).
% 5.51/5.78  thf('129', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.51/5.78      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.51/5.78  thf('130', plain,
% 5.51/5.78      (((r1_orders_2 @ sk_A @ 
% 5.51/5.78         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78         sk_B)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B)
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['128', '129'])).
% 5.51/5.78  thf('131', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (r1_orders_2 @ sk_A @ 
% 5.51/5.78           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78           sk_B))),
% 5.51/5.78      inference('sup-', [status(thm)], ['47', '130'])).
% 5.51/5.78  thf('132', plain,
% 5.51/5.78      (((r1_orders_2 @ sk_A @ 
% 5.51/5.78         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78         sk_B)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('simplify', [status(thm)], ['131'])).
% 5.51/5.78  thf('133', plain,
% 5.51/5.78      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.51/5.78         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 5.51/5.78          | ~ (r1_orders_2 @ X11 @ X8 @ X10))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.51/5.78  thf('134', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B @ sk_A)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (zip_tseitin_0 @ 
% 5.51/5.78             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78             X0 @ sk_B @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['132', '133'])).
% 5.51/5.78  thf('135', plain,
% 5.51/5.78      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.51/5.78          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.51/5.78  thf('136', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         (((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_1 @ 
% 5.51/5.78             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78             X0 @ sk_B @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['134', '135'])).
% 5.51/5.78  thf('137', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.51/5.78      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.51/5.78  thf('138', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B)
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['136', '137'])).
% 5.51/5.78  thf('139', plain,
% 5.51/5.78      ((~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('simplify', [status(thm)], ['138'])).
% 5.51/5.78  thf('140', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['46', '139'])).
% 5.51/5.78  thf('141', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('simplify', [status(thm)], ['140'])).
% 5.51/5.78  thf('142', plain,
% 5.51/5.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.51/5.78         (((X18) = (k2_yellow_0 @ X16 @ X17))
% 5.51/5.78          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.51/5.78  thf('143', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['141', '142'])).
% 5.51/5.78  thf('144', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('simplify', [status(thm)], ['143'])).
% 5.51/5.78  thf('145', plain, (~ (v2_struct_0 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('146', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('clc', [status(thm)], ['144', '145'])).
% 5.51/5.78  thf('147', plain,
% 5.51/5.78      (![X40 : $i]:
% 5.51/5.78         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 5.51/5.78          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('148', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E @ sk_A)) @ sk_A @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['146', '147'])).
% 5.51/5.78  thf('149', plain,
% 5.51/5.78      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 5.51/5.78         ((v2_struct_0 @ X31)
% 5.51/5.78          | ~ (v4_orders_2 @ X31)
% 5.51/5.78          | ~ (v7_waybel_0 @ X31)
% 5.51/5.78          | ~ (l1_waybel_0 @ X31 @ X32)
% 5.51/5.78          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 5.51/5.78          | (r1_lattice3 @ X32 @ 
% 5.51/5.78             (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 5.51/5.78              (u1_waybel_0 @ X32 @ X31)) @ 
% 5.51/5.78             X33)
% 5.51/5.78          | ((X34) != (X33))
% 5.51/5.78          | ~ (r3_waybel_9 @ X32 @ X31 @ X34)
% 5.51/5.78          | ~ (v11_waybel_0 @ X31 @ X32)
% 5.51/5.78          | ~ (v5_pre_topc @ (k4_waybel_1 @ X32 @ (sk_E @ X32)) @ X32 @ X32)
% 5.51/5.78          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 5.51/5.78          | ~ (l1_waybel_9 @ X32)
% 5.51/5.78          | ~ (v1_compts_1 @ X32)
% 5.51/5.78          | ~ (v2_lattice3 @ X32)
% 5.51/5.78          | ~ (v1_lattice3 @ X32)
% 5.51/5.78          | ~ (v5_orders_2 @ X32)
% 5.51/5.78          | ~ (v4_orders_2 @ X32)
% 5.51/5.78          | ~ (v3_orders_2 @ X32)
% 5.51/5.78          | ~ (v8_pre_topc @ X32)
% 5.51/5.78          | ~ (v2_pre_topc @ X32))),
% 5.51/5.78      inference('cnf', [status(esa)], [l51_waybel_9])).
% 5.51/5.78  thf('150', plain,
% 5.51/5.78      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.51/5.78         (~ (v2_pre_topc @ X32)
% 5.51/5.78          | ~ (v8_pre_topc @ X32)
% 5.51/5.78          | ~ (v3_orders_2 @ X32)
% 5.51/5.78          | ~ (v4_orders_2 @ X32)
% 5.51/5.78          | ~ (v5_orders_2 @ X32)
% 5.51/5.78          | ~ (v1_lattice3 @ X32)
% 5.51/5.78          | ~ (v2_lattice3 @ X32)
% 5.51/5.78          | ~ (v1_compts_1 @ X32)
% 5.51/5.78          | ~ (l1_waybel_9 @ X32)
% 5.51/5.78          | ~ (v5_pre_topc @ (k4_waybel_1 @ X32 @ (sk_E @ X32)) @ X32 @ X32)
% 5.51/5.78          | ~ (v11_waybel_0 @ X31 @ X32)
% 5.51/5.78          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 5.51/5.78          | (r1_lattice3 @ X32 @ 
% 5.51/5.78             (k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32) @ 
% 5.51/5.78              (u1_waybel_0 @ X32 @ X31)) @ 
% 5.51/5.78             X33)
% 5.51/5.78          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 5.51/5.78          | ~ (l1_waybel_0 @ X31 @ X32)
% 5.51/5.78          | ~ (v7_waybel_0 @ X31)
% 5.51/5.78          | ~ (v4_orders_2 @ X31)
% 5.51/5.78          | (v2_struct_0 @ X31))),
% 5.51/5.78      inference('simplify', [status(thm)], ['149'])).
% 5.51/5.78  thf('151', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (v2_struct_0 @ X0)
% 5.51/5.78          | ~ (v4_orders_2 @ X0)
% 5.51/5.78          | ~ (v7_waybel_0 @ X0)
% 5.51/5.78          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_lattice3 @ sk_A @ 
% 5.51/5.78             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78              (u1_waybel_0 @ sk_A @ X0)) @ 
% 5.51/5.78             X1)
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 5.51/5.78          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 5.51/5.78          | ~ (l1_waybel_9 @ sk_A)
% 5.51/5.78          | ~ (v1_compts_1 @ sk_A)
% 5.51/5.78          | ~ (v2_lattice3 @ sk_A)
% 5.51/5.78          | ~ (v1_lattice3 @ sk_A)
% 5.51/5.78          | ~ (v5_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v4_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v3_orders_2 @ sk_A)
% 5.51/5.78          | ~ (v8_pre_topc @ sk_A)
% 5.51/5.78          | ~ (v2_pre_topc @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['148', '150'])).
% 5.51/5.78  thf('152', plain, ((l1_waybel_9 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('153', plain, ((v1_compts_1 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('154', plain, ((v2_lattice3 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('155', plain, ((v1_lattice3 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('156', plain, ((v5_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('157', plain, ((v4_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('158', plain, ((v3_orders_2 @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('159', plain, ((v8_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('160', plain, ((v2_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('161', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (v2_struct_0 @ X0)
% 5.51/5.78          | ~ (v4_orders_2 @ X0)
% 5.51/5.78          | ~ (v7_waybel_0 @ X0)
% 5.51/5.78          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_lattice3 @ sk_A @ 
% 5.51/5.78             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78              (u1_waybel_0 @ sk_A @ X0)) @ 
% 5.51/5.78             X1)
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 5.51/5.78          | ~ (v11_waybel_0 @ X0 @ sk_A))),
% 5.51/5.78      inference('demod', [status(thm)],
% 5.51/5.78                ['151', '152', '153', '154', '155', '156', '157', '158', 
% 5.51/5.78                 '159', '160'])).
% 5.51/5.78  thf('162', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         (~ (v11_waybel_0 @ X0 @ sk_A)
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | (r1_lattice3 @ sk_A @ 
% 5.51/5.78             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78              (u1_waybel_0 @ sk_A @ X0)) @ 
% 5.51/5.78             sk_B)
% 5.51/5.78          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 5.51/5.78          | ~ (v7_waybel_0 @ X0)
% 5.51/5.78          | ~ (v4_orders_2 @ X0)
% 5.51/5.78          | (v2_struct_0 @ X0)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['12', '161'])).
% 5.51/5.78  thf('163', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | ~ (v4_orders_2 @ sk_C)
% 5.51/5.78        | ~ (v7_waybel_0 @ sk_C)
% 5.51/5.78        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 5.51/5.78        | (r1_lattice3 @ sk_A @ 
% 5.51/5.78           (k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78            (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78        | ~ (v11_waybel_0 @ sk_C @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['11', '162'])).
% 5.51/5.78  thf('164', plain, ((v4_orders_2 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('165', plain, ((v7_waybel_0 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('166', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('167', plain,
% 5.51/5.78      (((k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78         (u1_waybel_0 @ sk_A @ sk_C))
% 5.51/5.78         = (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 5.51/5.78      inference('sup-', [status(thm)], ['38', '39'])).
% 5.51/5.78  thf('168', plain, ((v11_waybel_0 @ sk_C @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('169', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           sk_B))),
% 5.51/5.78      inference('demod', [status(thm)],
% 5.51/5.78                ['163', '164', '165', '166', '167', '168'])).
% 5.51/5.78  thf('170', plain, (~ (v2_struct_0 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('171', plain,
% 5.51/5.78      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('clc', [status(thm)], ['169', '170'])).
% 5.51/5.78  thf('172', plain,
% 5.51/5.78      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('clc', [status(thm)], ['169', '170'])).
% 5.51/5.78  thf('173', plain,
% 5.51/5.78      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('clc', [status(thm)], ['169', '170'])).
% 5.51/5.78  thf('174', plain,
% 5.51/5.78      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.51/5.78          | (m1_subset_1 @ X12 @ (u1_struct_0 @ X15)))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.51/5.78  thf('175', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.51/5.78      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.51/5.78  thf('176', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['174', '175'])).
% 5.51/5.78  thf('177', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ 
% 5.51/5.78           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78           (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('sup-', [status(thm)], ['173', '176'])).
% 5.51/5.78  thf('178', plain,
% 5.51/5.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.51/5.78         (((X18) = (k2_yellow_0 @ X16 @ X17))
% 5.51/5.78          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.51/5.78  thf('179', plain,
% 5.51/5.78      (((m1_subset_1 @ 
% 5.51/5.78         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78         (u1_struct_0 @ sk_A))
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('clc', [status(thm)], ['177', '178'])).
% 5.51/5.78  thf('180', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('181', plain,
% 5.51/5.78      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.51/5.78         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11) | (r1_lattice3 @ X11 @ X9 @ X8))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.51/5.78  thf('182', plain,
% 5.51/5.78      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('clc', [status(thm)], ['169', '170'])).
% 5.51/5.78  thf('183', plain,
% 5.51/5.78      (((r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('clc', [status(thm)], ['169', '170'])).
% 5.51/5.78  thf('184', plain,
% 5.51/5.78      (((v2_struct_0 @ sk_C)
% 5.51/5.78        | (r1_orders_2 @ sk_A @ 
% 5.51/5.78           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B)
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['80', '86'])).
% 5.51/5.78  thf('185', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (r1_orders_2 @ sk_A @ 
% 5.51/5.78           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78        | (v2_struct_0 @ sk_C))),
% 5.51/5.78      inference('sup-', [status(thm)], ['183', '184'])).
% 5.51/5.78  thf('186', plain,
% 5.51/5.78      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.51/5.78         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 5.51/5.78          | ~ (r1_orders_2 @ X11 @ X8 @ X10))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.51/5.78  thf('187', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((v2_struct_0 @ sk_C)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B @ sk_A)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (zip_tseitin_0 @ 
% 5.51/5.78             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78             X0 @ sk_B @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['185', '186'])).
% 5.51/5.78  thf('188', plain,
% 5.51/5.78      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.78         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.51/5.78          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.51/5.78  thf('189', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         (((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B @ sk_A)
% 5.51/5.78          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (zip_tseitin_1 @ 
% 5.51/5.78             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78             X0 @ sk_B @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['187', '188'])).
% 5.51/5.78  thf('190', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.51/5.78          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.51/5.78      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.51/5.78  thf('191', plain,
% 5.51/5.78      (((v2_struct_0 @ sk_C)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             sk_B)
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['189', '190'])).
% 5.51/5.78  thf('192', plain,
% 5.51/5.78      ((~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (v2_struct_0 @ sk_C))),
% 5.51/5.78      inference('simplify', [status(thm)], ['191'])).
% 5.51/5.78  thf('193', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78           sk_A)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['182', '192'])).
% 5.51/5.78  thf('194', plain,
% 5.51/5.78      (((zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.78         sk_A)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('simplify', [status(thm)], ['193'])).
% 5.51/5.78  thf('195', plain,
% 5.51/5.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.51/5.78         (((X18) = (k2_yellow_0 @ X16 @ X17))
% 5.51/5.78          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.51/5.78  thf('196', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['194', '195'])).
% 5.51/5.78  thf('197', plain,
% 5.51/5.78      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.51/5.78        | (v2_struct_0 @ sk_C)
% 5.51/5.78        | ((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('simplify', [status(thm)], ['196'])).
% 5.51/5.78  thf('198', plain, (~ (v2_struct_0 @ sk_C)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('199', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('clc', [status(thm)], ['197', '198'])).
% 5.51/5.78  thf('200', plain,
% 5.51/5.78      (![X40 : $i]:
% 5.51/5.78         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 5.51/5.78          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('201', plain,
% 5.51/5.78      ((((sk_B)
% 5.51/5.78          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['199', '200'])).
% 5.51/5.78  thf('202', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X0)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.51/5.78          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 5.51/5.78               sk_A))),
% 5.51/5.78      inference('demod', [status(thm)],
% 5.51/5.78                ['105', '106', '107', '108', '109', '110', '111', '112', 
% 5.51/5.78                 '113', '114', '115', '116', '117'])).
% 5.51/5.78  thf('203', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X0)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X1 @ X0)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ~ (r1_lattice3 @ sk_A @ 
% 5.51/5.78               (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X1))),
% 5.51/5.78      inference('sup-', [status(thm)], ['201', '202'])).
% 5.51/5.78  thf('204', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.51/5.78         ((zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78           X2 @ sk_A)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ X1)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['181', '203'])).
% 5.51/5.78  thf('205', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | ~ (r3_waybel_9 @ sk_A @ sk_C @ sk_B)
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X1 @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['180', '204'])).
% 5.51/5.78  thf('206', plain, ((r3_waybel_9 @ sk_A @ sk_C @ sk_B)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('207', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]:
% 5.51/5.78         (((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.51/5.78          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.78             X1 @ sk_A))),
% 5.51/5.78      inference('demod', [status(thm)], ['205', '206'])).
% 5.51/5.78  thf('208', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         (((sk_B)
% 5.51/5.78            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.78          | (zip_tseitin_0 @ 
% 5.51/5.78             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X0 @ sk_A)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (r1_orders_2 @ sk_A @ 
% 5.51/5.78             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78             sk_B)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['179', '207'])).
% 5.51/5.78  thf('209', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         ((r1_orders_2 @ sk_A @ 
% 5.51/5.78           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78           sk_B)
% 5.51/5.78          | (v2_struct_0 @ sk_C)
% 5.51/5.78          | (zip_tseitin_0 @ 
% 5.51/5.78             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.78             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X0 @ sk_A)
% 5.51/5.78          | ((sk_B)
% 5.51/5.78              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.78                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.78      inference('simplify', [status(thm)], ['208'])).
% 5.51/5.78  thf('210', plain,
% 5.51/5.78      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.79         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.51/5.79          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.51/5.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.51/5.79  thf('211', plain,
% 5.51/5.79      (![X0 : $i]:
% 5.51/5.79         (((sk_B)
% 5.51/5.79            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.79          | (v2_struct_0 @ sk_C)
% 5.51/5.79          | (r1_orders_2 @ sk_A @ 
% 5.51/5.79             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.79             sk_B)
% 5.51/5.79          | (zip_tseitin_1 @ 
% 5.51/5.79             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.79             (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ X0 @ sk_A))),
% 5.51/5.79      inference('sup-', [status(thm)], ['209', '210'])).
% 5.51/5.79  thf('212', plain,
% 5.51/5.79      (![X0 : $i]:
% 5.51/5.79         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.51/5.79          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.51/5.79          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.51/5.79      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.51/5.79  thf('213', plain,
% 5.51/5.79      (((r1_orders_2 @ sk_A @ 
% 5.51/5.79         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.79         sk_B)
% 5.51/5.79        | (v2_struct_0 @ sk_C)
% 5.51/5.79        | ((sk_B)
% 5.51/5.79            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.79        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.79             sk_B)
% 5.51/5.79        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.79           sk_A))),
% 5.51/5.79      inference('sup-', [status(thm)], ['211', '212'])).
% 5.51/5.79  thf('214', plain,
% 5.51/5.79      ((((sk_B)
% 5.51/5.79          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.79        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.79           sk_A)
% 5.51/5.79        | ((sk_B)
% 5.51/5.79            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.79        | (v2_struct_0 @ sk_C)
% 5.51/5.79        | (r1_orders_2 @ sk_A @ 
% 5.51/5.79           (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.79           sk_B))),
% 5.51/5.79      inference('sup-', [status(thm)], ['172', '213'])).
% 5.51/5.79  thf('215', plain,
% 5.51/5.79      (((r1_orders_2 @ sk_A @ 
% 5.51/5.79         (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.79         sk_B)
% 5.51/5.79        | (v2_struct_0 @ sk_C)
% 5.51/5.79        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.79           sk_A)
% 5.51/5.79        | ((sk_B)
% 5.51/5.79            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.79      inference('simplify', [status(thm)], ['214'])).
% 5.51/5.79  thf('216', plain,
% 5.51/5.79      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.51/5.79         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 5.51/5.79          | ~ (r1_orders_2 @ X11 @ X8 @ X10))),
% 5.51/5.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.51/5.79  thf('217', plain,
% 5.51/5.79      (![X0 : $i]:
% 5.51/5.79         (((sk_B)
% 5.51/5.79            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.79          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.79             sk_B @ sk_A)
% 5.51/5.79          | (v2_struct_0 @ sk_C)
% 5.51/5.79          | (zip_tseitin_0 @ 
% 5.51/5.79             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.79             X0 @ sk_B @ sk_A))),
% 5.51/5.79      inference('sup-', [status(thm)], ['215', '216'])).
% 5.51/5.79  thf('218', plain,
% 5.51/5.79      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.79         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 5.51/5.79          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 5.51/5.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.51/5.79  thf('219', plain,
% 5.51/5.79      (![X0 : $i]:
% 5.51/5.79         ((v2_struct_0 @ sk_C)
% 5.51/5.79          | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.79             sk_B @ sk_A)
% 5.51/5.79          | ((sk_B)
% 5.51/5.79              = (k2_yellow_0 @ sk_A @ 
% 5.51/5.79                 (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.79          | (zip_tseitin_1 @ 
% 5.51/5.79             (sk_D @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ sk_A) @ 
% 5.51/5.79             X0 @ sk_B @ sk_A))),
% 5.51/5.79      inference('sup-', [status(thm)], ['217', '218'])).
% 5.51/5.79  thf('220', plain,
% 5.51/5.79      (![X0 : $i]:
% 5.51/5.79         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 5.51/5.79          | ~ (zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 5.51/5.79          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))),
% 5.51/5.79      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.51/5.79  thf('221', plain,
% 5.51/5.79      ((((sk_B)
% 5.51/5.79          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.79        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.79           sk_A)
% 5.51/5.79        | (v2_struct_0 @ sk_C)
% 5.51/5.79        | ~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.79             sk_B)
% 5.51/5.79        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.79           sk_A))),
% 5.51/5.79      inference('sup-', [status(thm)], ['219', '220'])).
% 5.51/5.79  thf('222', plain,
% 5.51/5.79      ((~ (r1_lattice3 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ 
% 5.51/5.79           sk_B)
% 5.51/5.79        | (v2_struct_0 @ sk_C)
% 5.51/5.79        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.79           sk_A)
% 5.51/5.79        | ((sk_B)
% 5.51/5.79            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.79      inference('simplify', [status(thm)], ['221'])).
% 5.51/5.79  thf('223', plain,
% 5.51/5.79      ((((sk_B)
% 5.51/5.79          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.79        | ((sk_B)
% 5.51/5.79            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.79        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.79           sk_A)
% 5.51/5.79        | (v2_struct_0 @ sk_C))),
% 5.51/5.79      inference('sup-', [status(thm)], ['171', '222'])).
% 5.51/5.79  thf('224', plain,
% 5.51/5.79      (((v2_struct_0 @ sk_C)
% 5.51/5.79        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.79           sk_A)
% 5.51/5.79        | ((sk_B)
% 5.51/5.79            = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)))))),
% 5.51/5.79      inference('simplify', [status(thm)], ['223'])).
% 5.51/5.79  thf('225', plain, (~ (v2_struct_0 @ sk_C)),
% 5.51/5.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.79  thf('226', plain,
% 5.51/5.79      ((((sk_B)
% 5.51/5.79          = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))
% 5.51/5.79        | (zip_tseitin_2 @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C)) @ sk_B @ 
% 5.51/5.79           sk_A))),
% 5.51/5.79      inference('clc', [status(thm)], ['224', '225'])).
% 5.51/5.79  thf('227', plain,
% 5.51/5.79      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.51/5.79         (((X18) = (k2_yellow_0 @ X16 @ X17))
% 5.51/5.79          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 5.51/5.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.51/5.79  thf('228', plain,
% 5.51/5.79      (((sk_B)
% 5.51/5.79         = (k2_yellow_0 @ sk_A @ (k2_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))))),
% 5.51/5.79      inference('clc', [status(thm)], ['226', '227'])).
% 5.51/5.79  thf('229', plain,
% 5.51/5.79      ((((sk_B) = (k5_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))
% 5.51/5.79        | ~ (l1_orders_2 @ sk_A)
% 5.51/5.79        | ~ (v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))
% 5.51/5.79        | ~ (v1_lattice3 @ sk_A))),
% 5.51/5.79      inference('sup+', [status(thm)], ['10', '228'])).
% 5.51/5.79  thf('230', plain, ((l1_orders_2 @ sk_A)),
% 5.51/5.79      inference('sup-', [status(thm)], ['3', '4'])).
% 5.51/5.79  thf('231', plain,
% 5.51/5.79      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 5.51/5.79        (k1_zfmisc_1 @ 
% 5.51/5.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 5.51/5.79      inference('demod', [status(thm)], ['34', '37'])).
% 5.51/5.79  thf(cc1_relset_1, axiom,
% 5.51/5.79    (![A:$i,B:$i,C:$i]:
% 5.51/5.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.51/5.79       ( v1_relat_1 @ C ) ))).
% 5.51/5.79  thf('232', plain,
% 5.51/5.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.51/5.79         ((v1_relat_1 @ X0)
% 5.51/5.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 5.51/5.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.51/5.79  thf('233', plain, ((v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C))),
% 5.51/5.79      inference('sup-', [status(thm)], ['231', '232'])).
% 5.51/5.79  thf('234', plain, ((v1_lattice3 @ sk_A)),
% 5.51/5.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.79  thf('235', plain,
% 5.51/5.79      (((sk_B) = (k5_yellow_2 @ sk_A @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 5.51/5.79      inference('demod', [status(thm)], ['229', '230', '233', '234'])).
% 5.51/5.79  thf('236', plain,
% 5.51/5.79      ((((sk_B) = (k1_waybel_9 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 5.51/5.79      inference('sup+', [status(thm)], ['6', '235'])).
% 5.51/5.79  thf('237', plain, (((sk_B) != (k1_waybel_9 @ sk_A @ sk_C))),
% 5.51/5.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.79  thf('238', plain, ((v2_struct_0 @ sk_A)),
% 5.51/5.79      inference('simplify_reflect-', [status(thm)], ['236', '237'])).
% 5.51/5.79  thf('239', plain,
% 5.51/5.79      (![X7 : $i]:
% 5.51/5.79         (~ (v1_lattice3 @ X7) | ~ (v2_struct_0 @ X7) | ~ (l1_orders_2 @ X7))),
% 5.51/5.79      inference('cnf', [status(esa)], [cc1_lattice3])).
% 5.51/5.79  thf('240', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 5.51/5.79      inference('sup-', [status(thm)], ['238', '239'])).
% 5.51/5.79  thf('241', plain, ((l1_orders_2 @ sk_A)),
% 5.51/5.79      inference('sup-', [status(thm)], ['3', '4'])).
% 5.51/5.79  thf('242', plain, ((v1_lattice3 @ sk_A)),
% 5.51/5.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.79  thf('243', plain, ($false),
% 5.51/5.79      inference('demod', [status(thm)], ['240', '241', '242'])).
% 5.51/5.79  
% 5.51/5.79  % SZS output end Refutation
% 5.51/5.79  
% 5.51/5.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
