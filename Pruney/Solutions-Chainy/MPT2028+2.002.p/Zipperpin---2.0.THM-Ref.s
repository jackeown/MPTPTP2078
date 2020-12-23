%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NuBU6g7cfo

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 196 expanded)
%              Number of leaves         :   38 (  74 expanded)
%              Depth                    :   27
%              Number of atoms          : 1231 (3159 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k6_waybel_0_type,type,(
    k6_waybel_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

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
    ! [X15: $i] :
      ( ( l1_orders_2 @ X15 )
      | ~ ( l1_waybel_9 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('1',plain,(
    ! [X15: $i] :
      ( ( l1_pre_topc @ X15 )
      | ~ ( l1_waybel_9 @ X15 ) ) ),
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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X16 ) @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t10_pcomps_1])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i] :
      ( ( l1_pre_topc @ X15 )
      | ~ ( l1_waybel_9 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('15',plain,(
    ! [X15: $i] :
      ( ( l1_orders_2 @ X15 )
      | ~ ( l1_waybel_9 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_waybel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k4_waybel_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('18',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i] :
      ( ( l1_orders_2 @ X15 )
      | ~ ( l1_waybel_9 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('25',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X15: $i] :
      ( ( l1_orders_2 @ X15 )
      | ~ ( l1_waybel_9 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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

thf('36',plain,(
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

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B ) @ sk_A @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X20: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X20 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','46'])).

thf('48',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X15: $i] :
      ( ( l1_orders_2 @ X15 )
      | ~ ( l1_waybel_9 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X19 ) @ ( k4_waybel_1 @ X19 @ X18 ) @ ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ X18 ) )
        = ( k6_waybel_0 @ X19 @ X18 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v2_lattice3 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_waybel_9])).

thf('56',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k6_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','63'])).

thf('65',plain,(
    ~ ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X15: $i] :
      ( ( l1_orders_2 @ X15 )
      | ~ ( l1_waybel_9 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k6_waybel_0 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_waybel_0])).

thf('70',plain,
    ( ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v1_xboole_0 @ ( k6_waybel_0 @ A @ B ) )
        & ( v2_waybel_0 @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) )).

thf('79',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_xboole_0 @ ( k6_waybel_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_waybel_0])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','84'])).

thf('86',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X15: $i] :
      ( ( l1_orders_2 @ X15 )
      | ~ ( l1_waybel_9 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('89',plain,(
    ! [X8: $i] :
      ( ~ ( v1_lattice3 @ X8 )
      | ~ ( v2_struct_0 @ X8 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['91','92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NuBU6g7cfo
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 62 iterations in 0.025s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.51  thf(k6_waybel_0_type, type, k6_waybel_0: $i > $i > $i).
% 0.21/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.21/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.51  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.21/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.21/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.51  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(dt_l1_waybel_9, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.21/0.51  thf('0', plain, (![X15 : $i]: ((l1_orders_2 @ X15) | ~ (l1_waybel_9 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.51  thf('1', plain, (![X15 : $i]: ((l1_pre_topc @ X15) | ~ (l1_waybel_9 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.51  thf(t27_waybel_9, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.21/0.51         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ( ![C:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                 ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.21/0.51             ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.21/0.51            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51              ( ( ![C:$i]:
% 0.21/0.51                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                    ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.21/0.51                ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t27_waybel_9])).
% 0.21/0.51  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t10_pcomps_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ( v8_pre_topc @ A ) =>
% 0.21/0.51             ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.51          | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X16) @ X17)
% 0.21/0.51          | ~ (v8_pre_topc @ X17)
% 0.21/0.51          | ~ (l1_pre_topc @ X17)
% 0.21/0.51          | ~ (v2_pre_topc @ X17)
% 0.21/0.51          | (v2_struct_0 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_pcomps_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.51        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.21/0.51        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.51  thf('9', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (((v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k6_domain_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X6)
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ X6)
% 0.21/0.51          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X15 : $i]: ((l1_pre_topc @ X15) | ~ (l1_waybel_9 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X15 : $i]: ((l1_orders_2 @ X15) | ~ (l1_waybel_9 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.51  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k4_waybel_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.21/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.21/0.51         ( v1_funct_2 @
% 0.21/0.51           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           ( k4_waybel_1 @ A @ B ) @ 
% 0.21/0.51           ( k1_zfmisc_1 @
% 0.21/0.51             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ X13)
% 0.21/0.51          | (v2_struct_0 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.51          | (v1_funct_1 @ (k4_waybel_1 @ X13 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.51  thf('20', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X15 : $i]: ((l1_orders_2 @ X15) | ~ (l1_waybel_9 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.51  thf('23', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ X13)
% 0.21/0.51          | (v2_struct_0 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.51          | (v1_funct_2 @ (k4_waybel_1 @ X13 @ X14) @ (u1_struct_0 @ X13) @ 
% 0.21/0.51             (u1_struct_0 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51         (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51           (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.51  thf('27', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51           (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X15 : $i]: ((l1_orders_2 @ X15) | ~ (l1_waybel_9 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.51  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ X13)
% 0.21/0.51          | (v2_struct_0 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.51          | (m1_subset_1 @ (k4_waybel_1 @ X13 @ X14) @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X13)))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51         (k1_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '32'])).
% 0.21/0.51  thf('34', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf(d12_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( l1_pre_topc @ B ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.21/0.51                 ( ![D:$i]:
% 0.21/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51                     ( ( v4_pre_topc @ D @ B ) =>
% 0.21/0.51                       ( v4_pre_topc @
% 0.21/0.51                         ( k8_relset_1 @
% 0.21/0.51                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.21/0.51                         A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X2)
% 0.21/0.51          | ~ (v5_pre_topc @ X3 @ X4 @ X2)
% 0.21/0.51          | ~ (v4_pre_topc @ X5 @ X2)
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k8_relset_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X2) @ X3 @ X5) @ 
% 0.21/0.51             X4)
% 0.21/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X2))))
% 0.21/0.51          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X2))
% 0.21/0.51          | ~ (v1_funct_1 @ X3)
% 0.21/0.51          | ~ (l1_pre_topc @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             sk_A)
% 0.21/0.51          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X20 : $i]:
% 0.21/0.51         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X20) @ sk_A @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('40', plain, ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             sk_A)
% 0.21/0.51          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             sk_A)
% 0.21/0.51          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             sk_A)
% 0.21/0.51          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_waybel_9 @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             sk_A)
% 0.21/0.51          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '46'])).
% 0.21/0.51  thf('48', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             sk_A)
% 0.21/0.51          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.51        | (v4_pre_topc @ 
% 0.21/0.51           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.21/0.51           sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v4_pre_topc @ 
% 0.21/0.51           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.21/0.51           sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v4_pre_topc @ 
% 0.21/0.51           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.21/0.51           sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X15 : $i]: ((l1_orders_2 @ X15) | ~ (l1_waybel_9 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.51  thf('54', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t7_waybel_9, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.21/0.51         ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ( k8_relset_1 @
% 0.21/0.51               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.51               ( k4_waybel_1 @ A @ B ) @ 
% 0.21/0.51               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.21/0.51             ( k6_waybel_0 @ A @ B ) ) ) ) ))).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.21/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X19) @ 
% 0.21/0.51              (k4_waybel_1 @ X19 @ X18) @ 
% 0.21/0.51              (k6_domain_1 @ (u1_struct_0 @ X19) @ X18))
% 0.21/0.51              = (k6_waybel_0 @ X19 @ X18))
% 0.21/0.51          | ~ (l1_orders_2 @ X19)
% 0.21/0.51          | ~ (v2_lattice3 @ X19)
% 0.21/0.51          | ~ (v5_orders_2 @ X19)
% 0.21/0.51          | ~ (v3_orders_2 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_waybel_9])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((~ (v3_orders_2 @ sk_A)
% 0.21/0.51        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.51        | ~ (v2_lattice3 @ sk_A)
% 0.21/0.51        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('58', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain, ((v2_lattice3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.21/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '60'])).
% 0.21/0.51  thf('62', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51         (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51         = (k6_waybel_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['52', '63'])).
% 0.21/0.51  thf('65', plain, (~ (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (![X15 : $i]: ((l1_orders_2 @ X15) | ~ (l1_waybel_9 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.51  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k6_waybel_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.21/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @
% 0.21/0.51         ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ X9)
% 0.21/0.51          | (v2_struct_0 @ X9)
% 0.21/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.21/0.51          | (m1_subset_1 @ (k6_waybel_0 @ X9 @ X10) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_waybel_0])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (((m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '70'])).
% 0.21/0.51  thf('72', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.51  thf(cc1_subset_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.51          | (v1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['66', '75'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (((v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['76'])).
% 0.21/0.51  thf('78', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(fc9_waybel_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( ( ~( v1_xboole_0 @ ( k6_waybel_0 @ A @ B ) ) ) & 
% 0.21/0.51         ( v2_waybel_0 @ ( k6_waybel_0 @ A @ B ) @ A ) ) ))).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ X11)
% 0.21/0.51          | ~ (v3_orders_2 @ X11)
% 0.21/0.51          | (v2_struct_0 @ X11)
% 0.21/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.21/0.51          | ~ (v1_xboole_0 @ (k6_waybel_0 @ X11 @ X12)))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc9_waybel_0])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.51  thf('81', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['80', '81'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A) | ~ (l1_orders_2 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['77', '82'])).
% 0.21/0.51  thf('84', plain, ((~ (l1_orders_2 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['83'])).
% 0.21/0.51  thf('85', plain, ((~ (l1_waybel_9 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '84'])).
% 0.21/0.51  thf('86', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('87', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['85', '86'])).
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      (![X15 : $i]: ((l1_orders_2 @ X15) | ~ (l1_waybel_9 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.51  thf(cc1_lattice3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ A ) =>
% 0.21/0.51       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      (![X8 : $i]:
% 0.21/0.51         (~ (v1_lattice3 @ X8) | ~ (v2_struct_0 @ X8) | ~ (l1_orders_2 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.21/0.51  thf('90', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v1_lattice3 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.51  thf('91', plain, ((~ (v1_lattice3 @ sk_A) | ~ (l1_waybel_9 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['87', '90'])).
% 0.21/0.51  thf('92', plain, ((v1_lattice3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('93', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('94', plain, ($false),
% 0.21/0.51      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
