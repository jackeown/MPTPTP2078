%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M68om4Sy9O

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:32 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 196 expanded)
%              Number of leaves         :   39 (  76 expanded)
%              Depth                    :   28
%              Number of atoms          : 1126 (3006 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(k6_waybel_0_type,type,(
    k6_waybel_0: $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( l1_orders_2 @ X12 )
      | ~ ( l1_waybel_9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( l1_pre_topc @ X12 )
      | ~ ( l1_waybel_9 @ X12 ) ) ),
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

thf('3',plain,(
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

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ~ ( v8_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_pcomps_1])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i] :
      ( ( l1_pre_topc @ X12 )
      | ~ ( l1_waybel_9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('16',plain,(
    ! [X12: $i] :
      ( ( l1_orders_2 @ X12 )
      | ~ ( l1_waybel_9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('19',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X12: $i] :
      ( ( l1_orders_2 @ X12 )
      | ~ ( l1_waybel_9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('26',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X12: $i] :
      ( ( l1_orders_2 @ X12 )
      | ~ ( l1_waybel_9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X10 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

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

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v5_pre_topc @ X1 @ X2 @ X0 )
      | ~ ( v4_pre_topc @ X3 @ X0 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X1 @ X3 ) @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('38',plain,(
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
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X17: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X17 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','47'])).

thf('49',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','50'])).

thf('52',plain,(
    ! [X12: $i] :
      ( ( l1_orders_2 @ X12 )
      | ~ ( l1_waybel_9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X16 ) @ ( k4_waybel_1 @ X16 @ X15 ) @ ( k6_domain_1 @ ( u1_struct_0 @ X16 ) @ X15 ) )
        = ( k6_waybel_0 @ X16 @ X15 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_lattice3 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_waybel_9])).

thf('55',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k6_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ~ ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','67'])).

thf('69',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X12: $i] :
      ( ( l1_orders_2 @ X12 )
      | ~ ( l1_waybel_9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('71',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X12: $i] :
      ( ( l1_orders_2 @ X12 )
      | ~ ( l1_waybel_9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('76',plain,(
    ! [X8: $i] :
      ( ~ ( v1_lattice3 @ X8 )
      | ~ ( v2_struct_0 @ X8 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf(fc2_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('82',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','83'])).

thf('85',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('88',plain,
    ( ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['88','89','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M68om4Sy9O
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:30:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 117 iterations in 0.067s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.34/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.34/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.34/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.34/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.34/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.34/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.34/0.53  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.34/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.34/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.34/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.34/0.53  thf(k6_waybel_0_type, type, k6_waybel_0: $i > $i > $i).
% 0.34/0.53  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.34/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.34/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.53  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.34/0.53  thf(dt_l1_waybel_9, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.34/0.53  thf('0', plain, (![X12 : $i]: ((l1_orders_2 @ X12) | ~ (l1_waybel_9 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.34/0.53  thf(d3_struct_0, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      (![X4 : $i]:
% 0.34/0.53         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.34/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.53  thf('2', plain, (![X12 : $i]: ((l1_pre_topc @ X12) | ~ (l1_waybel_9 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.34/0.53  thf(t27_waybel_9, conjecture,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.34/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.34/0.53         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.53           ( ( ![C:$i]:
% 0.34/0.53               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.53                 ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.34/0.53             ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i]:
% 0.34/0.53        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.34/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.34/0.53            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.34/0.53          ( ![B:$i]:
% 0.34/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.53              ( ( ![C:$i]:
% 0.34/0.53                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.53                    ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.34/0.53                ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t27_waybel_9])).
% 0.34/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t10_pcomps_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.53           ( ( v8_pre_topc @ A ) =>
% 0.34/0.53             ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (![X13 : $i, X14 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.34/0.53          | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 0.34/0.53          | ~ (v8_pre_topc @ X14)
% 0.34/0.53          | ~ (l1_pre_topc @ X14)
% 0.34/0.53          | ~ (v2_pre_topc @ X14)
% 0.34/0.53          | (v2_struct_0 @ X14))),
% 0.34/0.53      inference('cnf', [status(esa)], [t10_pcomps_1])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | ~ (v8_pre_topc @ sk_A)
% 0.34/0.53        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.34/0.53  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('7', plain, ((v8_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      ((~ (l1_waybel_9 @ sk_A)
% 0.34/0.53        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.34/0.53        | (v2_struct_0 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['2', '8'])).
% 0.34/0.53  thf('10', plain, ((l1_waybel_9 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (((v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.34/0.53        | (v2_struct_0 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.34/0.53  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(dt_k6_domain_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.34/0.53       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (![X5 : $i, X6 : $i]:
% 0.34/0.53         ((v1_xboole_0 @ X5)
% 0.34/0.53          | ~ (m1_subset_1 @ X6 @ X5)
% 0.34/0.53          | (m1_subset_1 @ (k6_domain_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.34/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (![X12 : $i]: ((l1_pre_topc @ X12) | ~ (l1_waybel_9 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (![X12 : $i]: ((l1_orders_2 @ X12) | ~ (l1_waybel_9 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.34/0.53  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(dt_k4_waybel_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.34/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.34/0.53         ( v1_funct_2 @
% 0.34/0.53           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.34/0.53         ( m1_subset_1 @
% 0.34/0.53           ( k4_waybel_1 @ A @ B ) @ 
% 0.34/0.53           ( k1_zfmisc_1 @
% 0.34/0.53             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (![X10 : $i, X11 : $i]:
% 0.34/0.53         (~ (l1_orders_2 @ X10)
% 0.34/0.53          | (v2_struct_0 @ X10)
% 0.34/0.53          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.34/0.53          | (v1_funct_1 @ (k4_waybel_1 @ X10 @ X11)))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.34/0.53        | (v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (l1_orders_2 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      ((~ (l1_waybel_9 @ sk_A)
% 0.34/0.53        | (v2_struct_0 @ sk_A)
% 0.34/0.53        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['16', '19'])).
% 0.34/0.53  thf('21', plain, ((l1_waybel_9 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.34/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X12 : $i]: ((l1_orders_2 @ X12) | ~ (l1_waybel_9 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.34/0.53  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('25', plain,
% 0.34/0.53      (![X10 : $i, X11 : $i]:
% 0.34/0.53         (~ (l1_orders_2 @ X10)
% 0.34/0.53          | (v2_struct_0 @ X10)
% 0.34/0.53          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.34/0.53          | (v1_funct_2 @ (k4_waybel_1 @ X10 @ X11) @ (u1_struct_0 @ X10) @ 
% 0.34/0.53             (u1_struct_0 @ X10)))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.53         (u1_struct_0 @ sk_A))
% 0.34/0.53        | (v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (l1_orders_2 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      ((~ (l1_waybel_9 @ sk_A)
% 0.34/0.53        | (v2_struct_0 @ sk_A)
% 0.34/0.53        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.53           (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['23', '26'])).
% 0.34/0.53  thf('28', plain, ((l1_waybel_9 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('29', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.53           (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      (![X12 : $i]: ((l1_orders_2 @ X12) | ~ (l1_waybel_9 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.34/0.53  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('32', plain,
% 0.34/0.53      (![X10 : $i, X11 : $i]:
% 0.34/0.53         (~ (l1_orders_2 @ X10)
% 0.34/0.53          | (v2_struct_0 @ X10)
% 0.34/0.53          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.34/0.53          | (m1_subset_1 @ (k4_waybel_1 @ X10 @ X11) @ 
% 0.34/0.53             (k1_zfmisc_1 @ 
% 0.34/0.53              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X10)))))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.34/0.53         (k1_zfmisc_1 @ 
% 0.34/0.53          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.34/0.53        | (v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (l1_orders_2 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      ((~ (l1_waybel_9 @ sk_A)
% 0.34/0.53        | (v2_struct_0 @ sk_A)
% 0.34/0.53        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.34/0.53           (k1_zfmisc_1 @ 
% 0.34/0.53            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['30', '33'])).
% 0.34/0.53  thf('35', plain, ((l1_waybel_9 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.34/0.53           (k1_zfmisc_1 @ 
% 0.34/0.53            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.34/0.53  thf(d12_pre_topc, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_pre_topc @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( l1_pre_topc @ B ) =>
% 0.34/0.53           ( ![C:$i]:
% 0.34/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.34/0.53                 ( m1_subset_1 @
% 0.34/0.53                   C @ 
% 0.34/0.53                   ( k1_zfmisc_1 @
% 0.34/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.34/0.53               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.34/0.53                 ( ![D:$i]:
% 0.34/0.53                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.34/0.53                     ( ( v4_pre_topc @ D @ B ) =>
% 0.34/0.53                       ( v4_pre_topc @
% 0.34/0.53                         ( k8_relset_1 @
% 0.34/0.53                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.34/0.53                         A ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.53  thf('37', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.53         (~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (v5_pre_topc @ X1 @ X2 @ X0)
% 0.34/0.53          | ~ (v4_pre_topc @ X3 @ X0)
% 0.34/0.53          | (v4_pre_topc @ 
% 0.34/0.53             (k8_relset_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X1 @ X3) @ 
% 0.34/0.53             X2)
% 0.34/0.53          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.34/0.53          | ~ (m1_subset_1 @ X1 @ 
% 0.34/0.53               (k1_zfmisc_1 @ 
% 0.34/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.34/0.53          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.34/0.53          | ~ (v1_funct_1 @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.34/0.53  thf('38', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((v2_struct_0 @ sk_A)
% 0.34/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.34/0.53          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.34/0.53               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.34/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.53          | (v4_pre_topc @ 
% 0.34/0.53             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.53              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.34/0.53             sk_A)
% 0.34/0.53          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.34/0.53          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)
% 0.34/0.53          | ~ (l1_pre_topc @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.34/0.53  thf('39', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('40', plain,
% 0.34/0.53      (![X17 : $i]:
% 0.34/0.53         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X17) @ sk_A @ sk_A)
% 0.34/0.53          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('41', plain, ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 0.34/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.53  thf('42', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((v2_struct_0 @ sk_A)
% 0.34/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.34/0.53          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.34/0.53               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.34/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.53          | (v4_pre_topc @ 
% 0.34/0.53             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.53              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.34/0.53             sk_A)
% 0.34/0.53          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.34/0.53          | ~ (l1_pre_topc @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['38', '41'])).
% 0.34/0.53  thf('43', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.34/0.53          | (v4_pre_topc @ 
% 0.34/0.53             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.36/0.53             sk_A)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.36/0.53               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.36/0.53          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.36/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53          | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.53  thf('44', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v2_struct_0 @ sk_A)
% 0.36/0.53          | (v2_struct_0 @ sk_A)
% 0.36/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | (v4_pre_topc @ 
% 0.36/0.53             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.36/0.53             sk_A)
% 0.36/0.53          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['29', '43'])).
% 0.36/0.53  thf('45', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.36/0.53          | (v4_pre_topc @ 
% 0.36/0.53             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.36/0.53             sk_A)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.36/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53          | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.36/0.53  thf('46', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v2_struct_0 @ sk_A)
% 0.36/0.53          | (v2_struct_0 @ sk_A)
% 0.36/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | (v4_pre_topc @ 
% 0.36/0.53             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.36/0.53             sk_A)
% 0.36/0.53          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['22', '45'])).
% 0.36/0.53  thf('47', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.36/0.53          | (v4_pre_topc @ 
% 0.36/0.53             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.36/0.53             sk_A)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53          | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('simplify', [status(thm)], ['46'])).
% 0.36/0.53  thf('48', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (l1_waybel_9 @ sk_A)
% 0.36/0.53          | (v2_struct_0 @ sk_A)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | (v4_pre_topc @ 
% 0.36/0.53             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.36/0.53             sk_A)
% 0.36/0.53          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['15', '47'])).
% 0.36/0.53  thf('49', plain, ((l1_waybel_9 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('50', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v2_struct_0 @ sk_A)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | (v4_pre_topc @ 
% 0.36/0.53             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.36/0.53             sk_A)
% 0.36/0.53          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['48', '49'])).
% 0.36/0.53  thf('51', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | ~ (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.36/0.53        | (v4_pre_topc @ 
% 0.36/0.53           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.36/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.36/0.53           sk_A)
% 0.36/0.53        | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['14', '50'])).
% 0.36/0.53  thf('52', plain,
% 0.36/0.53      (![X12 : $i]: ((l1_orders_2 @ X12) | ~ (l1_waybel_9 @ X12))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.36/0.53  thf('53', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t7_waybel_9, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.36/0.53         ( l1_orders_2 @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.53           ( ( k8_relset_1 @
% 0.36/0.53               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.53               ( k4_waybel_1 @ A @ B ) @ 
% 0.36/0.53               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.36/0.53             ( k6_waybel_0 @ A @ B ) ) ) ) ))).
% 0.36/0.53  thf('54', plain,
% 0.36/0.53      (![X15 : $i, X16 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.36/0.53          | ((k8_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X16) @ 
% 0.36/0.53              (k4_waybel_1 @ X16 @ X15) @ 
% 0.36/0.53              (k6_domain_1 @ (u1_struct_0 @ X16) @ X15))
% 0.36/0.53              = (k6_waybel_0 @ X16 @ X15))
% 0.36/0.53          | ~ (l1_orders_2 @ X16)
% 0.36/0.53          | ~ (v2_lattice3 @ X16)
% 0.36/0.53          | ~ (v5_orders_2 @ X16)
% 0.36/0.53          | ~ (v3_orders_2 @ X16))),
% 0.36/0.53      inference('cnf', [status(esa)], [t7_waybel_9])).
% 0.36/0.53  thf('55', plain,
% 0.36/0.53      ((~ (v3_orders_2 @ sk_A)
% 0.36/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.36/0.53        | ~ (v2_lattice3 @ sk_A)
% 0.36/0.53        | ~ (l1_orders_2 @ sk_A)
% 0.36/0.53        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.36/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.53            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.53  thf('56', plain, ((v3_orders_2 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('58', plain, ((v2_lattice3 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('59', plain,
% 0.36/0.53      ((~ (l1_orders_2 @ sk_A)
% 0.36/0.53        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.36/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.53            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.36/0.53      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.36/0.53  thf('60', plain,
% 0.36/0.53      ((~ (l1_waybel_9 @ sk_A)
% 0.36/0.53        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.36/0.53            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.53            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['52', '59'])).
% 0.36/0.53  thf('61', plain, ((l1_waybel_9 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('62', plain,
% 0.36/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.53         (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.36/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.53         = (k6_waybel_0 @ sk_A @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.53  thf('63', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | ~ (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.36/0.53        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.36/0.53        | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '62'])).
% 0.36/0.53  thf('64', plain,
% 0.36/0.53      (((v2_struct_0 @ sk_A)
% 0.36/0.53        | (v2_struct_0 @ sk_A)
% 0.36/0.53        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.36/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['11', '63'])).
% 0.36/0.53  thf('65', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.36/0.53        | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('simplify', [status(thm)], ['64'])).
% 0.36/0.53  thf('66', plain, (~ (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('67', plain,
% 0.36/0.53      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('clc', [status(thm)], ['65', '66'])).
% 0.36/0.53  thf('68', plain,
% 0.36/0.53      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.36/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.36/0.53        | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('sup+', [status(thm)], ['1', '67'])).
% 0.36/0.53  thf('69', plain, ((l1_waybel_9 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('70', plain,
% 0.36/0.53      (![X12 : $i]: ((l1_orders_2 @ X12) | ~ (l1_waybel_9 @ X12))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.36/0.53  thf(dt_l1_orders_2, axiom,
% 0.36/0.53    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.53  thf('71', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_orders_2 @ X7))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.36/0.53  thf('72', plain, (![X0 : $i]: (~ (l1_waybel_9 @ X0) | (l1_struct_0 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.53  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.53      inference('sup-', [status(thm)], ['69', '72'])).
% 0.36/0.53  thf('74', plain,
% 0.36/0.53      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['68', '73'])).
% 0.36/0.53  thf('75', plain,
% 0.36/0.53      (![X12 : $i]: ((l1_orders_2 @ X12) | ~ (l1_waybel_9 @ X12))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.36/0.53  thf(cc1_lattice3, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_orders_2 @ A ) =>
% 0.36/0.53       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.36/0.53  thf('76', plain,
% 0.36/0.53      (![X8 : $i]:
% 0.36/0.53         (~ (v1_lattice3 @ X8) | ~ (v2_struct_0 @ X8) | ~ (l1_orders_2 @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.36/0.53  thf('77', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v1_lattice3 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['75', '76'])).
% 0.36/0.53  thf('78', plain,
% 0.36/0.53      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.36/0.53        | ~ (v1_lattice3 @ sk_A)
% 0.36/0.53        | ~ (l1_waybel_9 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['74', '77'])).
% 0.36/0.53  thf('79', plain, ((v1_lattice3 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('80', plain, ((l1_waybel_9 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('81', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.36/0.53  thf(fc2_yellow_0, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.53       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.36/0.53  thf('82', plain,
% 0.36/0.53      (![X9 : $i]:
% 0.36/0.53         (~ (v1_xboole_0 @ (k2_struct_0 @ X9))
% 0.36/0.53          | ~ (l1_orders_2 @ X9)
% 0.36/0.53          | (v2_struct_0 @ X9))),
% 0.36/0.53      inference('cnf', [status(esa)], [fc2_yellow_0])).
% 0.36/0.53  thf('83', plain, (((v2_struct_0 @ sk_A) | ~ (l1_orders_2 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.36/0.53  thf('84', plain, ((~ (l1_waybel_9 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['0', '83'])).
% 0.36/0.53  thf('85', plain, ((l1_waybel_9 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('86', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.53      inference('demod', [status(thm)], ['84', '85'])).
% 0.36/0.53  thf('87', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v1_lattice3 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['75', '76'])).
% 0.36/0.53  thf('88', plain, ((~ (v1_lattice3 @ sk_A) | ~ (l1_waybel_9 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['86', '87'])).
% 0.36/0.53  thf('89', plain, ((v1_lattice3 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('90', plain, ((l1_waybel_9 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('91', plain, ($false),
% 0.36/0.53      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.36/0.53  
% 0.36/0.53  % SZS output end Refutation
% 0.36/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
