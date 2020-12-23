%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bJaMOhOeMT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 256 expanded)
%              Number of leaves         :   41 (  97 expanded)
%              Depth                    :   24
%              Number of atoms          : 1077 (4054 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(k6_waybel_0_type,type,(
    k6_waybel_0: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( l1_orders_2 @ X14 )
      | ~ ( l1_waybel_9 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('1',plain,(
    ! [X14: $i] :
      ( ( l1_orders_2 @ X14 )
      | ~ ( l1_waybel_9 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(t27_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_waybel_9 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) )
           => ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( v8_pre_topc @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( l1_waybel_9 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) )
             => ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_waybel_9])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X14: $i] :
      ( ( l1_pre_topc @ X14 )
      | ~ ( l1_waybel_9 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('6',plain,(
    ! [X14: $i] :
      ( ( l1_orders_2 @ X14 )
      | ~ ( l1_waybel_9 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_waybel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k4_waybel_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X14: $i] :
      ( ( l1_orders_2 @ X14 )
      | ~ ( l1_waybel_9 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ~ ( v2_lattice3 @ X10 )
      | ~ ( v2_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v2_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['9','16'])).

thf('18',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d12_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( v4_pre_topc @ D @ B )
                     => ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v5_pre_topc @ X3 @ X4 @ X2 )
      | ~ ( v4_pre_topc @ X5 @ X2 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X2 ) @ X3 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X14: $i] :
      ( ( l1_orders_2 @ X14 )
      | ~ ( l1_waybel_9 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('26',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('28',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X14: $i] :
      ( ( l1_orders_2 @ X14 )
      | ~ ( l1_waybel_9 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('35',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('37',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X19: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X19 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','31','40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','45'])).

thf('47',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','48'])).

thf('50',plain,(
    ! [X14: $i] :
      ( ( l1_pre_topc @ X14 )
      | ~ ( l1_waybel_9 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_pcomps_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v8_pre_topc @ A )
           => ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ~ ( v8_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t10_pcomps_1])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('58',plain,
    ( ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['49','61'])).

thf('63',plain,(
    ! [X14: $i] :
      ( ( l1_orders_2 @ X14 )
      | ~ ( l1_waybel_9 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('64',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( k4_waybel_1 @ A @ B ) @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k6_waybel_0 @ A @ B ) ) ) ) )).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X18 ) @ ( k4_waybel_1 @ X18 @ X17 ) @ ( k6_domain_1 @ ( u1_struct_0 @ X18 ) @ X17 ) )
        = ( k6_waybel_0 @ X18 @ X17 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v2_lattice3 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_waybel_9])).

thf('66',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k6_waybel_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k6_waybel_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k6_waybel_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k6_waybel_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','73'])).

thf('75',plain,(
    ~ ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf(rc11_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ? [B: $i] :
          ( ( v13_waybel_0 @ B @ A )
          & ( v12_waybel_0 @ B @ A )
          & ( v2_waybel_0 @ B @ A )
          & ( v1_waybel_0 @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('77',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( v1_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc11_waybel_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85'])).

thf('87',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','86'])).

thf('88',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_xboole_0 @ ( sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( v1_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc11_waybel_0])).

thf('91',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94','95','96'])).

thf('98',plain,(
    ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','97'])).

thf('99',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['98','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bJaMOhOeMT
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:08:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 103 iterations in 0.058s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(v1_waybel_0_type, type, v1_waybel_0: $i > $i > $o).
% 0.20/0.52  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(v12_waybel_0_type, type, v12_waybel_0: $i > $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.52  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.20/0.52  thf(k6_waybel_0_type, type, k6_waybel_0: $i > $i > $i).
% 0.20/0.52  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.52  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.20/0.52  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.20/0.52  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.20/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(dt_l1_waybel_9, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.20/0.52  thf('0', plain, (![X14 : $i]: ((l1_orders_2 @ X14) | ~ (l1_waybel_9 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.52  thf('1', plain, (![X14 : $i]: ((l1_orders_2 @ X14) | ~ (l1_waybel_9 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.52  thf(t27_waybel_9, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.20/0.52         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52           ( ( ![C:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52                 ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.20/0.52             ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.20/0.52            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52              ( ( ![C:$i]:
% 0.20/0.52                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52                    ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.20/0.52                ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t27_waybel_9])).
% 0.20/0.52  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k6_domain_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X6)
% 0.20/0.52          | ~ (m1_subset_1 @ X7 @ X6)
% 0.20/0.52          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain, (![X14 : $i]: ((l1_pre_topc @ X14) | ~ (l1_waybel_9 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.52  thf('6', plain, (![X14 : $i]: ((l1_orders_2 @ X14) | ~ (l1_waybel_9 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.52  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k4_waybel_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.20/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.20/0.52         ( v1_funct_2 @
% 0.20/0.52           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.52         ( m1_subset_1 @
% 0.20/0.52           ( k4_waybel_1 @ A @ B ) @ 
% 0.20/0.52           ( k1_zfmisc_1 @
% 0.20/0.52             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (l1_orders_2 @ X12)
% 0.20/0.52          | (v2_struct_0 @ X12)
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.52          | (m1_subset_1 @ (k4_waybel_1 @ X12 @ X13) @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X12)))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52         (k1_zfmisc_1 @ 
% 0.20/0.52          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X14 : $i]: ((l1_orders_2 @ X14) | ~ (l1_waybel_9 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.52  thf(cc2_lattice3, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_orders_2 @ A ) =>
% 0.20/0.52       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X10 : $i]:
% 0.20/0.52         (~ (v2_lattice3 @ X10) | ~ (v2_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_lattice3])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v2_lattice3 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain, ((~ (v2_struct_0 @ sk_A) | ~ (l1_waybel_9 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.52  thf('15', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.52        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52           (k1_zfmisc_1 @ 
% 0.20/0.52            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.52      inference('clc', [status(thm)], ['9', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.52        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52           (k1_zfmisc_1 @ 
% 0.20/0.52            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '17'])).
% 0.20/0.52  thf('19', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf(d12_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( l1_pre_topc @ B ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                 ( m1_subset_1 @
% 0.20/0.52                   C @ 
% 0.20/0.52                   ( k1_zfmisc_1 @
% 0.20/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.20/0.52                 ( ![D:$i]:
% 0.20/0.52                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.52                     ( ( v4_pre_topc @ D @ B ) =>
% 0.20/0.52                       ( v4_pre_topc @
% 0.20/0.52                         ( k8_relset_1 @
% 0.20/0.52                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.20/0.52                         A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X2)
% 0.20/0.52          | ~ (v5_pre_topc @ X3 @ X4 @ X2)
% 0.20/0.52          | ~ (v4_pre_topc @ X5 @ X2)
% 0.20/0.52          | (v4_pre_topc @ 
% 0.20/0.52             (k8_relset_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X2) @ X3 @ X5) @ 
% 0.20/0.52             X4)
% 0.20/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.52          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X2))))
% 0.20/0.52          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X2))
% 0.20/0.52          | ~ (v1_funct_1 @ X3)
% 0.20/0.52          | ~ (l1_pre_topc @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1))
% 0.20/0.52          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v4_pre_topc @ 
% 0.20/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.20/0.52             sk_A)
% 0.20/0.52          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B_1) @ sk_A @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X14 : $i]: ((l1_orders_2 @ X14) | ~ (l1_waybel_9 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.52  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (l1_orders_2 @ X12)
% 0.20/0.52          | (v2_struct_0 @ X12)
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.52          | (v1_funct_1 @ (k4_waybel_1 @ X12 @ X13)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((~ (l1_orders_2 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1)))),
% 0.20/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((~ (l1_waybel_9 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '28'])).
% 0.20/0.52  thf('30', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain, ((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X14 : $i]: ((l1_orders_2 @ X14) | ~ (l1_waybel_9 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.52  thf('33', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (l1_orders_2 @ X12)
% 0.20/0.52          | (v2_struct_0 @ X12)
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.52          | (v1_funct_2 @ (k4_waybel_1 @ X12 @ X13) @ (u1_struct_0 @ X12) @ 
% 0.20/0.52             (u1_struct_0 @ X12)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52         (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.52        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52           (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.52        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52           (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '37'])).
% 0.20/0.52  thf('39', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52        (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X19 : $i]:
% 0.20/0.52         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X19) @ sk_A @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B_1) @ sk_A @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v4_pre_topc @ 
% 0.20/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.20/0.52             sk_A)
% 0.20/0.52          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '31', '40', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | (v4_pre_topc @ 
% 0.20/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.20/0.52             sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_waybel_9 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v4_pre_topc @ 
% 0.20/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.20/0.52             sk_A)
% 0.20/0.52          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '45'])).
% 0.20/0.52  thf('47', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v4_pre_topc @ 
% 0.20/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.20/0.52             sk_A)
% 0.20/0.52          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.20/0.52        | (v4_pre_topc @ 
% 0.20/0.52           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.52           sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X14 : $i]: ((l1_pre_topc @ X14) | ~ (l1_waybel_9 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.52  thf('51', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t10_pcomps_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52           ( ( v8_pre_topc @ A ) =>
% 0.20/0.52             ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.20/0.52          | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ X16) @ X15) @ X16)
% 0.20/0.52          | ~ (v8_pre_topc @ X16)
% 0.20/0.52          | ~ (l1_pre_topc @ X16)
% 0.20/0.52          | ~ (v2_pre_topc @ X16)
% 0.20/0.52          | (v2_struct_0 @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [t10_pcomps_1])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v8_pre_topc @ sk_A)
% 0.20/0.52        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('55', plain, ((v8_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.52  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (((v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.52        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '58'])).
% 0.20/0.52  thf('60', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      ((v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v4_pre_topc @ 
% 0.20/0.52           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.52           sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '61'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X14 : $i]: ((l1_orders_2 @ X14) | ~ (l1_waybel_9 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.52  thf('64', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t7_waybel_9, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.20/0.52         ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52           ( ( k8_relset_1 @
% 0.20/0.52               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.52               ( k4_waybel_1 @ A @ B ) @ 
% 0.20/0.52               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.20/0.52             ( k6_waybel_0 @ A @ B ) ) ) ) ))).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.20/0.52          | ((k8_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18) @ 
% 0.20/0.52              (k4_waybel_1 @ X18 @ X17) @ 
% 0.20/0.52              (k6_domain_1 @ (u1_struct_0 @ X18) @ X17))
% 0.20/0.52              = (k6_waybel_0 @ X18 @ X17))
% 0.20/0.52          | ~ (l1_orders_2 @ X18)
% 0.20/0.52          | ~ (v2_lattice3 @ X18)
% 0.20/0.52          | ~ (v5_orders_2 @ X18)
% 0.20/0.52          | ~ (v3_orders_2 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_waybel_9])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      ((~ (v3_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v2_lattice3 @ sk_A)
% 0.20/0.52        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.20/0.52            = (k6_waybel_0 @ sk_A @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.52  thf('67', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('69', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.52        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.20/0.52            = (k6_waybel_0 @ sk_A @ sk_B_1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.52        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.20/0.52            = (k6_waybel_0 @ sk_A @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['63', '70'])).
% 0.20/0.52  thf('72', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52         (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.20/0.52         = (k6_waybel_0 @ sk_A @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['62', '73'])).
% 0.20/0.52  thf('75', plain, (~ (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('76', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf(rc11_waybel_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.20/0.52         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ?[B:$i]:
% 0.20/0.52         ( ( v13_waybel_0 @ B @ A ) & ( v12_waybel_0 @ B @ A ) & 
% 0.20/0.52           ( v2_waybel_0 @ B @ A ) & ( v1_waybel_0 @ B @ A ) & 
% 0.20/0.52           ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_B @ X11) @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.52          | ~ (l1_orders_2 @ X11)
% 0.20/0.52          | ~ (v2_lattice3 @ X11)
% 0.20/0.52          | ~ (v1_lattice3 @ X11)
% 0.20/0.52          | ~ (v5_orders_2 @ X11)
% 0.20/0.52          | ~ (v4_orders_2 @ X11)
% 0.20/0.52          | ~ (v3_orders_2 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc11_waybel_0])).
% 0.20/0.52  thf(cc1_subset_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.52          | (v1_xboole_0 @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v3_orders_2 @ X0)
% 0.20/0.52          | ~ (v4_orders_2 @ X0)
% 0.20/0.52          | ~ (v5_orders_2 @ X0)
% 0.20/0.52          | ~ (v1_lattice3 @ X0)
% 0.20/0.52          | ~ (v2_lattice3 @ X0)
% 0.20/0.52          | ~ (l1_orders_2 @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.52          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (((v1_xboole_0 @ (sk_B @ sk_A))
% 0.20/0.52        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v2_lattice3 @ sk_A)
% 0.20/0.52        | ~ (v1_lattice3 @ sk_A)
% 0.20/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v3_orders_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['76', '79'])).
% 0.20/0.52  thf('81', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('82', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('83', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('84', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('85', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('86', plain, (((v1_xboole_0 @ (sk_B @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['80', '81', '82', '83', '84', '85'])).
% 0.20/0.52  thf('87', plain, ((~ (l1_waybel_9 @ sk_A) | (v1_xboole_0 @ (sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '86'])).
% 0.20/0.52  thf('88', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('89', plain, ((v1_xboole_0 @ (sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['87', '88'])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (sk_B @ X11))
% 0.20/0.52          | ~ (l1_orders_2 @ X11)
% 0.20/0.52          | ~ (v2_lattice3 @ X11)
% 0.20/0.52          | ~ (v1_lattice3 @ X11)
% 0.20/0.52          | ~ (v5_orders_2 @ X11)
% 0.20/0.52          | ~ (v4_orders_2 @ X11)
% 0.20/0.52          | ~ (v3_orders_2 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc11_waybel_0])).
% 0.20/0.52  thf('91', plain,
% 0.20/0.52      ((~ (v3_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v1_lattice3 @ sk_A)
% 0.20/0.52        | ~ (v2_lattice3 @ sk_A)
% 0.20/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.52  thf('92', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('93', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('94', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('95', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('96', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('97', plain, (~ (l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['91', '92', '93', '94', '95', '96'])).
% 0.20/0.52  thf('98', plain, (~ (l1_waybel_9 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '97'])).
% 0.20/0.52  thf('99', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('100', plain, ($false), inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
