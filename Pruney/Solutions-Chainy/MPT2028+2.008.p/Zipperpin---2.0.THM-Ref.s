%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KDRFFevbUw

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 269 expanded)
%              Number of leaves         :   42 (  96 expanded)
%              Depth                    :   24
%              Number of atoms          : 1543 (4617 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_waybel_0_type,type,(
    k6_waybel_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ X25 )
      | ~ ( l1_waybel_9 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X13 @ X15 )
      | ~ ( r3_orders_2 @ X14 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ X25 )
      | ~ ( l1_waybel_9 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r3_orders_2 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_B @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ X25 )
      | ~ ( l1_waybel_9 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k6_waybel_0 @ A @ B ) )
              <=> ( r1_orders_2 @ A @ B @ C ) ) ) ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_orders_2 @ X21 @ X20 @ X22 )
      | ( r2_hidden @ X22 @ ( k6_waybel_0 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t18_waybel_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ X25 )
      | ~ ( l1_waybel_9 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X29 ) @ ( k4_waybel_1 @ X29 @ X28 ) @ ( k6_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 ) )
        = ( k6_waybel_0 @ X29 @ X28 ) )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_waybel_9])).

thf('37',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k6_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ X25 )
      | ~ ( l1_waybel_9 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X4 @ X5 @ X3 @ X6 ) @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['44','53'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X25: $i] :
      ( ( l1_pre_topc @ X25 )
      | ~ ( l1_waybel_9 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t10_pcomps_1])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('69',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X25: $i] :
      ( ( l1_pre_topc @ X25 )
      | ~ ( l1_waybel_9 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('71',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ X25 )
      | ~ ( l1_waybel_9 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('74',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ X25 )
      | ~ ( l1_waybel_9 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('81',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

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

thf('86',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v5_pre_topc @ X8 @ X9 @ X7 )
      | ~ ( v4_pre_topc @ X10 @ X7 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) @ X8 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('87',plain,(
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
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X30: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X30 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','96'])).

thf('98',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k6_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['56','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','107'])).

thf('109',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ X25 )
      | ~ ( l1_waybel_9 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('111',plain,(
    ! [X19: $i] :
      ( ~ ( v1_lattice3 @ X19 )
      | ~ ( v2_struct_0 @ X19 )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['113','114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KDRFFevbUw
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:30:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 77 iterations in 0.042s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.19/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.49  thf(k6_waybel_0_type, type, k6_waybel_0: $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.19/0.49  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.19/0.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.49  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.19/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.49  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.19/0.49  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.49  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.19/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.19/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(t27_waybel_9, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.19/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.19/0.49         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49           ( ( ![C:$i]:
% 0.19/0.49               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49                 ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.19/0.49             ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.19/0.49            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.19/0.49            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49              ( ( ![C:$i]:
% 0.19/0.49                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49                    ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.19/0.49                ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t27_waybel_9])).
% 0.19/0.49  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_l1_waybel_9, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.19/0.49  thf('1', plain, (![X25 : $i]: ((l1_orders_2 @ X25) | ~ (l1_waybel_9 @ X25))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.49  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(redefinition_r3_orders_2, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.49         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.19/0.49          | ~ (l1_orders_2 @ X14)
% 0.19/0.49          | ~ (v3_orders_2 @ X14)
% 0.19/0.49          | (v2_struct_0 @ X14)
% 0.19/0.49          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.19/0.49          | (r1_orders_2 @ X14 @ X13 @ X15)
% 0.19/0.49          | ~ (r3_orders_2 @ X14 @ X13 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.49          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.49          | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.49  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.49          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (l1_waybel_9 @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.49          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '6'])).
% 0.19/0.49  thf('8', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.49          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      ((~ (r3_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.19/0.49        | (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '9'])).
% 0.19/0.49  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X25 : $i]: ((l1_orders_2 @ X25) | ~ (l1_waybel_9 @ X25))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.49  thf('13', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(reflexivity_r3_orders_2, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.49         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49       ( r3_orders_2 @ A @ B @ B ) ))).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.49         ((r3_orders_2 @ X16 @ X17 @ X17)
% 0.19/0.49          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.19/0.49          | ~ (l1_orders_2 @ X16)
% 0.19/0.49          | ~ (v3_orders_2 @ X16)
% 0.19/0.49          | (v2_struct_0 @ X16)
% 0.19/0.49          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16)))),
% 0.19/0.49      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.19/0.49          | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('16', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.19/0.49          | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (l1_waybel_9 @ sk_A)
% 0.19/0.49          | (r3_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['12', '17'])).
% 0.19/0.49  thf('19', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r3_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A) | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '20'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.19/0.49      inference('clc', [status(thm)], ['10', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X25 : $i]: ((l1_orders_2 @ X25) | ~ (l1_waybel_9 @ X25))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.49  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t18_waybel_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49               ( ( r2_hidden @ C @ ( k6_waybel_0 @ A @ B ) ) <=>
% 0.19/0.49                 ( r1_orders_2 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.19/0.49          | ~ (r1_orders_2 @ X21 @ X20 @ X22)
% 0.19/0.49          | (r2_hidden @ X22 @ (k6_waybel_0 @ X21 @ X20))
% 0.19/0.49          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.19/0.49          | ~ (l1_orders_2 @ X21)
% 0.19/0.49          | (v2_struct_0 @ X21))),
% 0.19/0.49      inference('cnf', [status(esa)], [t18_waybel_0])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.19/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (l1_waybel_9 @ sk_A)
% 0.19/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.49          | (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '26'])).
% 0.19/0.49  thf('28', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.49          | (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | (r2_hidden @ sk_B @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '29'])).
% 0.19/0.49  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (r2_hidden @ sk_B @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (((r2_hidden @ sk_B @ (k6_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (![X25 : $i]: ((l1_orders_2 @ X25) | ~ (l1_waybel_9 @ X25))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.49  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t7_waybel_9, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.19/0.49         ( l1_orders_2 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49           ( ( k8_relset_1 @
% 0.19/0.49               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.49               ( k4_waybel_1 @ A @ B ) @ 
% 0.19/0.49               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.19/0.49             ( k6_waybel_0 @ A @ B ) ) ) ) ))).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (![X28 : $i, X29 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.19/0.49          | ((k8_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X29) @ 
% 0.19/0.49              (k4_waybel_1 @ X29 @ X28) @ 
% 0.19/0.49              (k6_domain_1 @ (u1_struct_0 @ X29) @ X28))
% 0.19/0.49              = (k6_waybel_0 @ X29 @ X28))
% 0.19/0.49          | ~ (l1_orders_2 @ X29)
% 0.19/0.49          | ~ (v2_lattice3 @ X29)
% 0.19/0.49          | ~ (v5_orders_2 @ X29)
% 0.19/0.49          | ~ (v3_orders_2 @ X29))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_waybel_9])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      ((~ (v3_orders_2 @ sk_A)
% 0.19/0.49        | ~ (v5_orders_2 @ sk_A)
% 0.19/0.49        | ~ (v2_lattice3 @ sk_A)
% 0.19/0.49        | ~ (l1_orders_2 @ sk_A)
% 0.19/0.49        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.49            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.49  thf('38', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('39', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('40', plain, ((v2_lattice3 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      ((~ (l1_orders_2 @ sk_A)
% 0.19/0.49        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.49            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.49        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.49            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['34', '41'])).
% 0.19/0.49  thf('43', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49         (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.49         = (k6_waybel_0 @ sk_A @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X25 : $i]: ((l1_orders_2 @ X25) | ~ (l1_waybel_9 @ X25))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.49  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_k4_waybel_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.19/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.19/0.49         ( v1_funct_2 @
% 0.19/0.49           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.49         ( m1_subset_1 @
% 0.19/0.49           ( k4_waybel_1 @ A @ B ) @ 
% 0.19/0.49           ( k1_zfmisc_1 @
% 0.19/0.49             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X23 : $i, X24 : $i]:
% 0.19/0.49         (~ (l1_orders_2 @ X23)
% 0.19/0.49          | (v2_struct_0 @ X23)
% 0.19/0.49          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.19/0.49          | (m1_subset_1 @ (k4_waybel_1 @ X23 @ X24) @ 
% 0.19/0.49             (k1_zfmisc_1 @ 
% 0.19/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X23)))))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49         (k1_zfmisc_1 @ 
% 0.19/0.49          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49           (k1_zfmisc_1 @ 
% 0.19/0.49            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['45', '48'])).
% 0.19/0.49  thf('50', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49           (k1_zfmisc_1 @ 
% 0.19/0.49            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.49  thf(dt_k8_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.19/0.49          | (m1_subset_1 @ (k8_relset_1 @ X4 @ X5 @ X3 @ X6) @ 
% 0.19/0.49             (k1_zfmisc_1 @ X4)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | (m1_subset_1 @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.49  thf('54', plain,
% 0.19/0.49      (((m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.19/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['44', '53'])).
% 0.19/0.49  thf(t5_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.19/0.49          ( v1_xboole_0 @ C ) ) ))).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.49          | ~ (v1_xboole_0 @ X2)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.49  thf('56', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | ~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.19/0.49  thf('57', plain,
% 0.19/0.49      (![X25 : $i]: ((l1_pre_topc @ X25) | ~ (l1_waybel_9 @ X25))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.49  thf('58', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t10_pcomps_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49           ( ( v8_pre_topc @ A ) =>
% 0.19/0.49             ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.19/0.49  thf('59', plain,
% 0.19/0.49      (![X26 : $i, X27 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.19/0.49          | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ X27) @ X26) @ X27)
% 0.19/0.49          | ~ (v8_pre_topc @ X27)
% 0.19/0.49          | ~ (l1_pre_topc @ X27)
% 0.19/0.49          | ~ (v2_pre_topc @ X27)
% 0.19/0.49          | (v2_struct_0 @ X27))),
% 0.19/0.49      inference('cnf', [status(esa)], [t10_pcomps_1])).
% 0.19/0.49  thf('60', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49        | ~ (v8_pre_topc @ sk_A)
% 0.19/0.49        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.49  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('62', plain, ((v8_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('63', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.19/0.49  thf('64', plain,
% 0.19/0.49      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.49        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['57', '63'])).
% 0.19/0.49  thf('65', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('66', plain,
% 0.19/0.49      (((v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['64', '65'])).
% 0.19/0.49  thf('67', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_k6_domain_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.49       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.49  thf('68', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ X11)
% 0.19/0.49          | ~ (m1_subset_1 @ X12 @ X11)
% 0.19/0.49          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.19/0.49  thf('69', plain,
% 0.19/0.49      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.19/0.49  thf('70', plain,
% 0.19/0.49      (![X25 : $i]: ((l1_pre_topc @ X25) | ~ (l1_waybel_9 @ X25))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.49  thf('71', plain,
% 0.19/0.49      (![X25 : $i]: ((l1_orders_2 @ X25) | ~ (l1_waybel_9 @ X25))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.49  thf('72', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('73', plain,
% 0.19/0.49      (![X23 : $i, X24 : $i]:
% 0.19/0.49         (~ (l1_orders_2 @ X23)
% 0.19/0.49          | (v2_struct_0 @ X23)
% 0.19/0.49          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.19/0.49          | (v1_funct_1 @ (k4_waybel_1 @ X23 @ X24)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.19/0.49  thf('74', plain,
% 0.19/0.49      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['72', '73'])).
% 0.19/0.49  thf('75', plain,
% 0.19/0.49      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['71', '74'])).
% 0.19/0.49  thf('76', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('77', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('demod', [status(thm)], ['75', '76'])).
% 0.19/0.49  thf('78', plain,
% 0.19/0.49      (![X25 : $i]: ((l1_orders_2 @ X25) | ~ (l1_waybel_9 @ X25))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.49  thf('79', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('80', plain,
% 0.19/0.49      (![X23 : $i, X24 : $i]:
% 0.19/0.49         (~ (l1_orders_2 @ X23)
% 0.19/0.49          | (v2_struct_0 @ X23)
% 0.19/0.49          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.19/0.49          | (v1_funct_2 @ (k4_waybel_1 @ X23 @ X24) @ (u1_struct_0 @ X23) @ 
% 0.19/0.49             (u1_struct_0 @ X23)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.19/0.49  thf('81', plain,
% 0.19/0.49      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49         (u1_struct_0 @ sk_A))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['79', '80'])).
% 0.19/0.49  thf('82', plain,
% 0.19/0.49      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49           (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['78', '81'])).
% 0.19/0.49  thf('83', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('84', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49           (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['82', '83'])).
% 0.19/0.49  thf('85', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49           (k1_zfmisc_1 @ 
% 0.19/0.49            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.49  thf(d12_pre_topc, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( l1_pre_topc @ B ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.49                 ( m1_subset_1 @
% 0.19/0.49                   C @ 
% 0.19/0.49                   ( k1_zfmisc_1 @
% 0.19/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.49               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.19/0.49                 ( ![D:$i]:
% 0.19/0.49                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.49                     ( ( v4_pre_topc @ D @ B ) =>
% 0.19/0.49                       ( v4_pre_topc @
% 0.19/0.49                         ( k8_relset_1 @
% 0.19/0.49                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.19/0.49                         A ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('86', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.49         (~ (l1_pre_topc @ X7)
% 0.19/0.49          | ~ (v5_pre_topc @ X8 @ X9 @ X7)
% 0.19/0.49          | ~ (v4_pre_topc @ X10 @ X7)
% 0.19/0.49          | (v4_pre_topc @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7) @ X8 @ X10) @ 
% 0.19/0.49             X9)
% 0.19/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.49          | ~ (m1_subset_1 @ X8 @ 
% 0.19/0.49               (k1_zfmisc_1 @ 
% 0.19/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))))
% 0.19/0.49          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))
% 0.19/0.49          | ~ (v1_funct_1 @ X8)
% 0.19/0.49          | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.19/0.49  thf('87', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.49          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49          | (v4_pre_topc @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.49             sk_A)
% 0.19/0.49          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.49          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['85', '86'])).
% 0.19/0.49  thf('88', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('89', plain,
% 0.19/0.49      (![X30 : $i]:
% 0.19/0.49         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X30) @ sk_A @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('90', plain, ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 0.19/0.49      inference('sup-', [status(thm)], ['88', '89'])).
% 0.19/0.49  thf('91', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.49          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49          | (v4_pre_topc @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.49             sk_A)
% 0.19/0.49          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['87', '90'])).
% 0.19/0.49  thf('92', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.49          | (v4_pre_topc @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.49             sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('simplify', [status(thm)], ['91'])).
% 0.19/0.49  thf('93', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49          | (v4_pre_topc @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.49             sk_A)
% 0.19/0.49          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['84', '92'])).
% 0.19/0.49  thf('94', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.49          | (v4_pre_topc @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.49             sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('simplify', [status(thm)], ['93'])).
% 0.19/0.49  thf('95', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49          | (v4_pre_topc @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.49             sk_A)
% 0.19/0.49          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['77', '94'])).
% 0.19/0.49  thf('96', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.49          | (v4_pre_topc @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.49             sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('simplify', [status(thm)], ['95'])).
% 0.19/0.49  thf('97', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (l1_waybel_9 @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49          | (v4_pre_topc @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.49             sk_A)
% 0.19/0.49          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['70', '96'])).
% 0.19/0.49  thf('98', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('99', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49          | (v4_pre_topc @ 
% 0.19/0.49             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.49             sk_A)
% 0.19/0.49          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['97', '98'])).
% 0.19/0.49  thf('100', plain,
% 0.19/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | ~ (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.49        | (v4_pre_topc @ 
% 0.19/0.49           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.19/0.49           sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['69', '99'])).
% 0.19/0.49  thf('101', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (v4_pre_topc @ 
% 0.19/0.49           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.19/0.49           sk_A)
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['66', '100'])).
% 0.19/0.49  thf('102', plain,
% 0.19/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | (v4_pre_topc @ 
% 0.19/0.49           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.19/0.49           sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('simplify', [status(thm)], ['101'])).
% 0.19/0.49  thf('103', plain,
% 0.19/0.49      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49         (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.49         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.49         = (k6_waybel_0 @ sk_A @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.19/0.49  thf('104', plain,
% 0.19/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['102', '103'])).
% 0.19/0.49  thf('105', plain, (~ (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('106', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('clc', [status(thm)], ['104', '105'])).
% 0.19/0.49  thf('107', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('clc', [status(thm)], ['56', '106'])).
% 0.19/0.49  thf('108', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['33', '107'])).
% 0.19/0.49  thf('109', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('simplify', [status(thm)], ['108'])).
% 0.19/0.49  thf('110', plain,
% 0.19/0.49      (![X25 : $i]: ((l1_orders_2 @ X25) | ~ (l1_waybel_9 @ X25))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.49  thf(cc1_lattice3, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_orders_2 @ A ) =>
% 0.19/0.49       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.19/0.49  thf('111', plain,
% 0.19/0.49      (![X19 : $i]:
% 0.19/0.49         (~ (v1_lattice3 @ X19) | ~ (v2_struct_0 @ X19) | ~ (l1_orders_2 @ X19))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.19/0.49  thf('112', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v1_lattice3 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['110', '111'])).
% 0.19/0.49  thf('113', plain, ((~ (v1_lattice3 @ sk_A) | ~ (l1_waybel_9 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['109', '112'])).
% 0.19/0.49  thf('114', plain, ((v1_lattice3 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('115', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('116', plain, ($false),
% 0.19/0.49      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
