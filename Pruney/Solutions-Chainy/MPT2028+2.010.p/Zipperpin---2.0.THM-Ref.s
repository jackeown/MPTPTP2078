%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b2qiRGdACa

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 173 expanded)
%              Number of leaves         :   37 (  68 expanded)
%              Depth                    :   24
%              Number of atoms          : 1088 (2730 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k6_waybel_0_type,type,(
    k6_waybel_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

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
    ! [X11: $i] :
      ( ( l1_pre_topc @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
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

thf('1',plain,(
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

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ~ ( v8_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t10_pcomps_1])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X11: $i] :
      ( ( l1_pre_topc @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('14',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('17',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X9 @ X10 ) @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('24',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

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

thf('35',plain,(
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

thf('36',plain,(
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
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X16: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X16 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','45'])).

thf('47',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X15 ) @ ( k4_waybel_1 @ X15 @ X14 ) @ ( k6_domain_1 @ ( u1_struct_0 @ X15 ) @ X14 ) )
        = ( k6_waybel_0 @ X15 @ X14 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v2_lattice3 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 ) ) ),
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
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','62'])).

thf('64',plain,(
    ~ ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('66',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X11: $i] :
      ( ( l1_pre_topc @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('70',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
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
    ( ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['78','79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b2qiRGdACa
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:18:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 48 iterations in 0.032s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.20/0.50  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.20/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k6_waybel_0_type, type, k6_waybel_0: $i > $i > $i).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.50  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(dt_l1_waybel_9, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.20/0.50  thf('0', plain, (![X11 : $i]: ((l1_pre_topc @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.50  thf(t27_waybel_9, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.20/0.50         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ( ![C:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                 ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.20/0.50             ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.20/0.50            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50              ( ( ![C:$i]:
% 0.20/0.50                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                    ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.20/0.50                ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t27_waybel_9])).
% 0.20/0.50  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t10_pcomps_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ( v8_pre_topc @ A ) =>
% 0.20/0.50             ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.50          | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.20/0.50          | ~ (v8_pre_topc @ X13)
% 0.20/0.50          | ~ (l1_pre_topc @ X13)
% 0.20/0.50          | ~ (v2_pre_topc @ X13)
% 0.20/0.50          | (v2_struct_0 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_pcomps_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v8_pre_topc @ sk_A)
% 0.20/0.50        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain, ((v8_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.50        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '6'])).
% 0.20/0.50  thf('8', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k6_domain_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X6)
% 0.20/0.50          | ~ (m1_subset_1 @ X7 @ X6)
% 0.20/0.50          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X11 : $i]: ((l1_pre_topc @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.50  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k4_waybel_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.20/0.50         ( v1_funct_2 @
% 0.20/0.50           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @
% 0.20/0.50           ( k4_waybel_1 @ A @ B ) @ 
% 0.20/0.50           ( k1_zfmisc_1 @
% 0.20/0.50             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ X9)
% 0.20/0.50          | (v2_struct_0 @ X9)
% 0.20/0.50          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.50          | (v1_funct_1 @ (k4_waybel_1 @ X9 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.50  thf('19', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.50  thf('22', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ X9)
% 0.20/0.50          | (v2_struct_0 @ X9)
% 0.20/0.50          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.50          | (v1_funct_2 @ (k4_waybel_1 @ X9 @ X10) @ (u1_struct_0 @ X9) @ 
% 0.20/0.50             (u1_struct_0 @ X9)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50         (u1_struct_0 @ sk_A))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50           (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '24'])).
% 0.20/0.50  thf('26', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50           (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.50  thf('29', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ X9)
% 0.20/0.50          | (v2_struct_0 @ X9)
% 0.20/0.50          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.50          | (m1_subset_1 @ (k4_waybel_1 @ X9 @ X10) @ 
% 0.20/0.50             (k1_zfmisc_1 @ 
% 0.20/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9)))))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50         (k1_zfmisc_1 @ 
% 0.20/0.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50           (k1_zfmisc_1 @ 
% 0.20/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.50  thf('33', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50           (k1_zfmisc_1 @ 
% 0.20/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf(d12_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_pre_topc @ B ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                 ( m1_subset_1 @
% 0.20/0.50                   C @ 
% 0.20/0.50                   ( k1_zfmisc_1 @
% 0.20/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.20/0.50                 ( ![D:$i]:
% 0.20/0.50                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.50                     ( ( v4_pre_topc @ D @ B ) =>
% 0.20/0.50                       ( v4_pre_topc @
% 0.20/0.50                         ( k8_relset_1 @
% 0.20/0.50                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.20/0.50                         A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v5_pre_topc @ X1 @ X2 @ X0)
% 0.20/0.50          | ~ (v4_pre_topc @ X3 @ X0)
% 0.20/0.50          | (v4_pre_topc @ 
% 0.20/0.50             (k8_relset_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X1 @ X3) @ 
% 0.20/0.50             X2)
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.20/0.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ~ (l1_pre_topc @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.50          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v4_pre_topc @ 
% 0.20/0.50             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.50             sk_A)
% 0.20/0.50          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X16 : $i]:
% 0.20/0.50         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X16) @ sk_A @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain, ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.50          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v4_pre_topc @ 
% 0.20/0.50             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.50             sk_A)
% 0.20/0.50          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (v4_pre_topc @ 
% 0.20/0.50             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.50             sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v4_pre_topc @ 
% 0.20/0.50             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.50             sk_A)
% 0.20/0.50          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (v4_pre_topc @ 
% 0.20/0.50             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.50             sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v4_pre_topc @ 
% 0.20/0.50             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.50             sk_A)
% 0.20/0.50          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (v4_pre_topc @ 
% 0.20/0.50             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.50             sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_waybel_9 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v4_pre_topc @ 
% 0.20/0.50             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.50             sk_A)
% 0.20/0.50          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '45'])).
% 0.20/0.50  thf('47', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v4_pre_topc @ 
% 0.20/0.50             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.50             sk_A)
% 0.20/0.50          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.50        | (v4_pre_topc @ 
% 0.20/0.50           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.50           sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v4_pre_topc @ 
% 0.20/0.50           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.50           sk_A)
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | (v4_pre_topc @ 
% 0.20/0.50           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.50           sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.50  thf('53', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t7_waybel_9, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.20/0.50         ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ( k8_relset_1 @
% 0.20/0.50               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.50               ( k4_waybel_1 @ A @ B ) @ 
% 0.20/0.50               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.20/0.50             ( k6_waybel_0 @ A @ B ) ) ) ) ))).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.20/0.50          | ((k8_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X15) @ 
% 0.20/0.50              (k4_waybel_1 @ X15 @ X14) @ 
% 0.20/0.50              (k6_domain_1 @ (u1_struct_0 @ X15) @ X14))
% 0.20/0.50              = (k6_waybel_0 @ X15 @ X14))
% 0.20/0.50          | ~ (l1_orders_2 @ X15)
% 0.20/0.50          | ~ (v2_lattice3 @ X15)
% 0.20/0.50          | ~ (v5_orders_2 @ X15)
% 0.20/0.50          | ~ (v3_orders_2 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_waybel_9])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((~ (v3_orders_2 @ sk_A)
% 0.20/0.50        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50        | ~ (v2_lattice3 @ sk_A)
% 0.20/0.50        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.50            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('58', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.50        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.50            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.50        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.50            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '59'])).
% 0.20/0.50  thf('61', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50         (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.50         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.50         = (k6_waybel_0 @ sk_A @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['51', '62'])).
% 0.20/0.50  thf('64', plain, (~ (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf(fc2_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (![X5 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ~ (l1_struct_0 @ X5)
% 0.20/0.50          | (v2_struct_0 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('68', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (![X11 : $i]: ((l1_pre_topc @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.50  thf(dt_l1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.50  thf('70', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('71', plain, (![X0 : $i]: (~ (l1_waybel_9 @ X0) | (l1_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['68', '71'])).
% 0.20/0.50  thf('73', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['67', '72'])).
% 0.20/0.50  thf('74', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.50  thf(cc1_lattice3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_orders_2 @ A ) =>
% 0.20/0.50       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      (![X8 : $i]:
% 0.20/0.50         (~ (v1_lattice3 @ X8) | ~ (v2_struct_0 @ X8) | ~ (l1_orders_2 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v1_lattice3 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('78', plain, ((~ (v1_lattice3 @ sk_A) | ~ (l1_waybel_9 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['74', '77'])).
% 0.20/0.50  thf('79', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('80', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('81', plain, ($false),
% 0.20/0.50      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
