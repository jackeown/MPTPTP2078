%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z1iretii6i

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 216 expanded)
%              Number of leaves         :   40 (  80 expanded)
%              Depth                    :   25
%              Number of atoms          : 1357 (3501 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k6_waybel_0_type,type,(
    k6_waybel_0: $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
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

thf(t24_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ B ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ X9 @ X9 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ( r2_hidden @ X16 @ ( k6_waybel_0 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t18_waybel_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X19: $i] :
      ( ( l1_pre_topc @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t10_pcomps_1])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X19: $i] :
      ( ( l1_pre_topc @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('34',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('37',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('44',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

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

thf('55',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v5_pre_topc @ X4 @ X5 @ X3 )
      | ~ ( v4_pre_topc @ X6 @ X3 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) @ X4 @ X6 ) @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('56',plain,(
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
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X24: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X24 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','65'])).

thf('67',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','68'])).

thf('70',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) @ ( k4_waybel_1 @ X23 @ X22 ) @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) )
        = ( k6_waybel_0 @ X23 @ X22 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_waybel_9])).

thf('73',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k6_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ~ ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('88',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( k6_waybel_0 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_waybel_0])).

thf('89',plain,
    ( ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','96'])).

thf('98',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('100',plain,(
    ! [X11: $i] :
      ( ~ ( v1_lattice3 @ X11 )
      | ~ ( v2_struct_0 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['102','103','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z1iretii6i
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:23:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 64 iterations in 0.025s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.48  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.22/0.48  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.22/0.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.22/0.48  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.22/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.48  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.22/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.48  thf(k6_waybel_0_type, type, k6_waybel_0: $i > $i > $i).
% 0.22/0.48  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.22/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(dt_l1_waybel_9, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.22/0.48  thf('0', plain, (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.48  thf(t27_waybel_9, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.22/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.22/0.48         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( ( ![C:$i]:
% 0.22/0.48               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48                 ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.22/0.48             ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.22/0.48            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.22/0.48            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48              ( ( ![C:$i]:
% 0.22/0.48                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48                    ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.22/0.48                ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t27_waybel_9])).
% 0.22/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t24_orders_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.22/0.48          | (r1_orders_2 @ X10 @ X9 @ X9)
% 0.22/0.48          | ~ (l1_orders_2 @ X10)
% 0.22/0.48          | ~ (v3_orders_2 @ X10)
% 0.22/0.48          | (v2_struct_0 @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (v3_orders_2 @ sk_A)
% 0.22/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.22/0.48        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.22/0.48        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.48        | (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.22/0.48        | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.48  thf('7', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (((r1_orders_2 @ sk_A @ sk_B @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf('9', plain, (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.48  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t18_waybel_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48               ( ( r2_hidden @ C @ ( k6_waybel_0 @ A @ B ) ) <=>
% 0.22/0.48                 ( r1_orders_2 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.22/0.48          | ~ (r1_orders_2 @ X15 @ X14 @ X16)
% 0.22/0.48          | (r2_hidden @ X16 @ (k6_waybel_0 @ X15 @ X14))
% 0.22/0.48          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.22/0.48          | ~ (l1_orders_2 @ X15)
% 0.22/0.48          | (v2_struct_0 @ X15))),
% 0.22/0.48      inference('cnf', [status(esa)], [t18_waybel_0])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v2_struct_0 @ sk_A)
% 0.22/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.22/0.48          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_waybel_9 @ sk_A)
% 0.22/0.48          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.22/0.48          | (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '12'])).
% 0.22/0.48  thf('14', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.22/0.48          | (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | (r2_hidden @ sk_B @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['8', '15'])).
% 0.22/0.48  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | (r2_hidden @ sk_B @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (((r2_hidden @ sk_B @ (k6_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X19 : $i]: ((l1_pre_topc @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.48  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t10_pcomps_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( ( v8_pre_topc @ A ) =>
% 0.22/0.48             ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X20 : $i, X21 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.22/0.48          | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.22/0.48          | ~ (v8_pre_topc @ X21)
% 0.22/0.48          | ~ (l1_pre_topc @ X21)
% 0.22/0.48          | ~ (v2_pre_topc @ X21)
% 0.22/0.48          | (v2_struct_0 @ X21))),
% 0.22/0.48      inference('cnf', [status(esa)], [t10_pcomps_1])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | ~ (v8_pre_topc @ sk_A)
% 0.22/0.48        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('25', plain, ((v8_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.48        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['20', '26'])).
% 0.22/0.48  thf('28', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (((v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.48  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_k6_domain_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.48       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X7)
% 0.22/0.48          | ~ (m1_subset_1 @ X8 @ X7)
% 0.22/0.48          | (m1_subset_1 @ (k6_domain_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.48  thf('32', plain,
% 0.22/0.48      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.48  thf('33', plain,
% 0.22/0.48      (![X19 : $i]: ((l1_pre_topc @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.48  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_k4_waybel_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.22/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.22/0.48         ( v1_funct_2 @
% 0.22/0.48           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.48         ( m1_subset_1 @
% 0.22/0.48           ( k4_waybel_1 @ A @ B ) @ 
% 0.22/0.48           ( k1_zfmisc_1 @
% 0.22/0.48             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.48  thf('36', plain,
% 0.22/0.48      (![X17 : $i, X18 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X17)
% 0.22/0.48          | (v2_struct_0 @ X17)
% 0.22/0.48          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.22/0.48          | (v1_funct_1 @ (k4_waybel_1 @ X17 @ X18)))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.22/0.48  thf('37', plain,
% 0.22/0.48      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.48  thf('38', plain,
% 0.22/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['34', '37'])).
% 0.22/0.48  thf('39', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('40', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.48  thf('41', plain,
% 0.22/0.48      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.48  thf('42', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('43', plain,
% 0.22/0.48      (![X17 : $i, X18 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X17)
% 0.22/0.48          | (v2_struct_0 @ X17)
% 0.22/0.48          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.22/0.48          | (v1_funct_2 @ (k4_waybel_1 @ X17 @ X18) @ (u1_struct_0 @ X17) @ 
% 0.22/0.48             (u1_struct_0 @ X17)))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.22/0.48  thf('44', plain,
% 0.22/0.48      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48         (u1_struct_0 @ sk_A))
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.48  thf('45', plain,
% 0.22/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48           (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['41', '44'])).
% 0.22/0.48  thf('46', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('47', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48           (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.48  thf('48', plain,
% 0.22/0.48      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.48  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('50', plain,
% 0.22/0.48      (![X17 : $i, X18 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X17)
% 0.22/0.48          | (v2_struct_0 @ X17)
% 0.22/0.48          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.22/0.48          | (m1_subset_1 @ (k4_waybel_1 @ X17 @ X18) @ 
% 0.22/0.48             (k1_zfmisc_1 @ 
% 0.22/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17)))))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.22/0.48  thf('51', plain,
% 0.22/0.48      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48         (k1_zfmisc_1 @ 
% 0.22/0.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.48  thf('52', plain,
% 0.22/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48           (k1_zfmisc_1 @ 
% 0.22/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['48', '51'])).
% 0.22/0.48  thf('53', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('54', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48           (k1_zfmisc_1 @ 
% 0.22/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.48      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.48  thf(d12_pre_topc, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( l1_pre_topc @ B ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.48                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.48                 ( m1_subset_1 @
% 0.22/0.48                   C @ 
% 0.22/0.48                   ( k1_zfmisc_1 @
% 0.22/0.48                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.48               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.22/0.48                 ( ![D:$i]:
% 0.22/0.48                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.48                     ( ( v4_pre_topc @ D @ B ) =>
% 0.22/0.48                       ( v4_pre_topc @
% 0.22/0.48                         ( k8_relset_1 @
% 0.22/0.48                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.22/0.48                         A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('55', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X3)
% 0.22/0.48          | ~ (v5_pre_topc @ X4 @ X5 @ X3)
% 0.22/0.48          | ~ (v4_pre_topc @ X6 @ X3)
% 0.22/0.48          | (v4_pre_topc @ 
% 0.22/0.48             (k8_relset_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3) @ X4 @ X6) @ 
% 0.22/0.48             X5)
% 0.22/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.22/0.48          | ~ (m1_subset_1 @ X4 @ 
% 0.22/0.48               (k1_zfmisc_1 @ 
% 0.22/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))))
% 0.22/0.48          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))
% 0.22/0.48          | ~ (v1_funct_1 @ X4)
% 0.22/0.48          | ~ (l1_pre_topc @ X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.22/0.48  thf('56', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v2_struct_0 @ sk_A)
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.22/0.48          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (v4_pre_topc @ 
% 0.22/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.48             sk_A)
% 0.22/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.48  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('58', plain,
% 0.22/0.48      (![X24 : $i]:
% 0.22/0.48         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X24) @ sk_A @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('59', plain, ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['57', '58'])).
% 0.22/0.48  thf('60', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v2_struct_0 @ sk_A)
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.22/0.48          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (v4_pre_topc @ 
% 0.22/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.48             sk_A)
% 0.22/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['56', '59'])).
% 0.22/0.48  thf('61', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | (v4_pre_topc @ 
% 0.22/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.48             sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48          | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('simplify', [status(thm)], ['60'])).
% 0.22/0.48  thf('62', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v2_struct_0 @ sk_A)
% 0.22/0.48          | (v2_struct_0 @ sk_A)
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (v4_pre_topc @ 
% 0.22/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.48             sk_A)
% 0.22/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['47', '61'])).
% 0.22/0.48  thf('63', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | (v4_pre_topc @ 
% 0.22/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.48             sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48          | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('simplify', [status(thm)], ['62'])).
% 0.22/0.48  thf('64', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v2_struct_0 @ sk_A)
% 0.22/0.48          | (v2_struct_0 @ sk_A)
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (v4_pre_topc @ 
% 0.22/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.48             sk_A)
% 0.22/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['40', '63'])).
% 0.22/0.48  thf('65', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | (v4_pre_topc @ 
% 0.22/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.48             sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48          | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('simplify', [status(thm)], ['64'])).
% 0.22/0.48  thf('66', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_waybel_9 @ sk_A)
% 0.22/0.48          | (v2_struct_0 @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (v4_pre_topc @ 
% 0.22/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.48             sk_A)
% 0.22/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['33', '65'])).
% 0.22/0.48  thf('67', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('68', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v2_struct_0 @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (v4_pre_topc @ 
% 0.22/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.48             sk_A)
% 0.22/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['66', '67'])).
% 0.22/0.48  thf('69', plain,
% 0.22/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | ~ (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.48        | (v4_pre_topc @ 
% 0.22/0.48           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.22/0.48           sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['32', '68'])).
% 0.22/0.48  thf('70', plain,
% 0.22/0.48      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.48  thf('71', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t7_waybel_9, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.22/0.48         ( l1_orders_2 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( ( k8_relset_1 @
% 0.22/0.48               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.48               ( k4_waybel_1 @ A @ B ) @ 
% 0.22/0.48               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.22/0.48             ( k6_waybel_0 @ A @ B ) ) ) ) ))).
% 0.22/0.48  thf('72', plain,
% 0.22/0.48      (![X22 : $i, X23 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.22/0.48          | ((k8_relset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X23) @ 
% 0.22/0.48              (k4_waybel_1 @ X23 @ X22) @ 
% 0.22/0.48              (k6_domain_1 @ (u1_struct_0 @ X23) @ X22))
% 0.22/0.48              = (k6_waybel_0 @ X23 @ X22))
% 0.22/0.48          | ~ (l1_orders_2 @ X23)
% 0.22/0.48          | ~ (v2_lattice3 @ X23)
% 0.22/0.48          | ~ (v5_orders_2 @ X23)
% 0.22/0.48          | ~ (v3_orders_2 @ X23))),
% 0.22/0.48      inference('cnf', [status(esa)], [t7_waybel_9])).
% 0.22/0.48  thf('73', plain,
% 0.22/0.48      ((~ (v3_orders_2 @ sk_A)
% 0.22/0.48        | ~ (v5_orders_2 @ sk_A)
% 0.22/0.48        | ~ (v2_lattice3 @ sk_A)
% 0.22/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.22/0.48        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.48            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.48  thf('74', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('75', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('76', plain, ((v2_lattice3 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('77', plain,
% 0.22/0.48      ((~ (l1_orders_2 @ sk_A)
% 0.22/0.48        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.48            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 0.22/0.48  thf('78', plain,
% 0.22/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.48        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.48            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['70', '77'])).
% 0.22/0.48  thf('79', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('80', plain,
% 0.22/0.48      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48         (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.22/0.48         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.48         = (k6_waybel_0 @ sk_A @ sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['78', '79'])).
% 0.22/0.48  thf('81', plain,
% 0.22/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | ~ (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.48        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['69', '80'])).
% 0.22/0.48  thf('82', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['29', '81'])).
% 0.22/0.48  thf('83', plain,
% 0.22/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('simplify', [status(thm)], ['82'])).
% 0.22/0.48  thf('84', plain, (~ (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('85', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('clc', [status(thm)], ['83', '84'])).
% 0.22/0.48  thf('86', plain,
% 0.22/0.48      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.48  thf('87', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_k6_waybel_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.22/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48       ( m1_subset_1 @
% 0.22/0.48         ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.48  thf('88', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X12)
% 0.22/0.48          | (v2_struct_0 @ X12)
% 0.22/0.48          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.22/0.48          | (m1_subset_1 @ (k6_waybel_0 @ X12 @ X13) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k6_waybel_0])).
% 0.22/0.48  thf('89', plain,
% 0.22/0.48      (((m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.22/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['87', '88'])).
% 0.22/0.48  thf('90', plain,
% 0.22/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.22/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['86', '89'])).
% 0.22/0.48  thf('91', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('92', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.22/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.48  thf(t5_subset, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.48          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.48  thf('93', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.48          | ~ (v1_xboole_0 @ X2)
% 0.22/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.48  thf('94', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v2_struct_0 @ sk_A)
% 0.22/0.48          | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['92', '93'])).
% 0.22/0.48  thf('95', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v2_struct_0 @ sk_A)
% 0.22/0.48          | ~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.22/0.48          | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['85', '94'])).
% 0.22/0.48  thf('96', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.22/0.48          | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('simplify', [status(thm)], ['95'])).
% 0.22/0.48  thf('97', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['19', '96'])).
% 0.22/0.48  thf('98', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.48      inference('simplify', [status(thm)], ['97'])).
% 0.22/0.48  thf('99', plain,
% 0.22/0.48      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.48  thf(cc1_lattice3, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.22/0.48  thf('100', plain,
% 0.22/0.48      (![X11 : $i]:
% 0.22/0.48         (~ (v1_lattice3 @ X11) | ~ (v2_struct_0 @ X11) | ~ (l1_orders_2 @ X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.22/0.48  thf('101', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v1_lattice3 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['99', '100'])).
% 0.22/0.48  thf('102', plain, ((~ (v1_lattice3 @ sk_A) | ~ (l1_waybel_9 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['98', '101'])).
% 0.22/0.48  thf('103', plain, ((v1_lattice3 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('104', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('105', plain, ($false),
% 0.22/0.48      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
