%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.67ozG3IkFs

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 243 expanded)
%              Number of leaves         :   42 (  88 expanded)
%              Depth                    :   25
%              Number of atoms          : 1543 (4043 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k6_waybel_0_type,type,(
    k6_waybel_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ X9 @ X11 )
      | ~ ( r3_orders_2 @ X10 @ X9 @ X11 ) ) ),
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
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r3_orders_2 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) ) ) ),
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
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ( r2_hidden @ X20 @ ( k6_waybel_0 @ X19 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X23: $i] :
      ( ( l1_pre_topc @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ~ ( v8_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_pcomps_1])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X23: $i] :
      ( ( l1_pre_topc @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('48',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('51',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('58',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X21 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('65',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

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

thf('69',plain,(
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

thf('70',plain,(
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
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X28: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X28 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','79'])).

thf('81',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X27 ) @ ( k4_waybel_1 @ X27 @ X26 ) @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) )
        = ( k6_waybel_0 @ X27 @ X26 ) )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v2_lattice3 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_waybel_9])).

thf('89',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k6_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','96'])).

thf('98',plain,(
    ~ ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('102',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ ( k6_waybel_0 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_waybel_0])).

thf('103',plain,
    ( ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','110'])).

thf('112',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('114',plain,(
    ! [X15: $i] :
      ( ~ ( v1_lattice3 @ X15 )
      | ~ ( v2_struct_0 @ X15 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['116','117','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.67ozG3IkFs
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:03:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 76 iterations in 0.051s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.20/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.48  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.20/0.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.20/0.48  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.48  thf(k6_waybel_0_type, type, k6_waybel_0: $i > $i > $i).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(t27_waybel_9, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.20/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.20/0.48         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48                 ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.20/0.48             ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.20/0.48            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.20/0.48            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( ( ![C:$i]:
% 0.20/0.48                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48                    ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.20/0.48                ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t27_waybel_9])).
% 0.20/0.48  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_l1_waybel_9, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.20/0.48  thf('1', plain, (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_r3_orders_2, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.48         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.20/0.48          | ~ (l1_orders_2 @ X10)
% 0.20/0.48          | ~ (v3_orders_2 @ X10)
% 0.20/0.48          | (v2_struct_0 @ X10)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.20/0.48          | (r1_orders_2 @ X10 @ X9 @ X11)
% 0.20/0.48          | ~ (r3_orders_2 @ X10 @ X9 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.48          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_waybel_9 @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.48  thf('8', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | ~ (r3_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((~ (r3_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.20/0.48        | (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '9'])).
% 0.20/0.48  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf('13', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(reflexivity_r3_orders_2, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.48         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( r3_orders_2 @ A @ B @ B ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.48         ((r3_orders_2 @ X12 @ X13 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.48          | ~ (l1_orders_2 @ X12)
% 0.20/0.48          | ~ (v3_orders_2 @ X12)
% 0.20/0.48          | (v2_struct_0 @ X12)
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12)))),
% 0.20/0.48      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_waybel_9 @ sk_A)
% 0.20/0.48          | (r3_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '17'])).
% 0.20/0.48  thf('19', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r3_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A) | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['10', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t18_waybel_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48               ( ( r2_hidden @ C @ ( k6_waybel_0 @ A @ B ) ) <=>
% 0.20/0.48                 ( r1_orders_2 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.20/0.48          | ~ (r1_orders_2 @ X19 @ X18 @ X20)
% 0.20/0.48          | (r2_hidden @ X20 @ (k6_waybel_0 @ X19 @ X18))
% 0.20/0.48          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.20/0.48          | ~ (l1_orders_2 @ X19)
% 0.20/0.48          | (v2_struct_0 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [t18_waybel_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.20/0.48          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_waybel_9 @ sk_A)
% 0.20/0.48          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.48  thf('28', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (r2_hidden @ sk_B @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '29'])).
% 0.20/0.48  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | (r2_hidden @ sk_B @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ (k6_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_pre_topc @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t10_pcomps_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( v8_pre_topc @ A ) =>
% 0.20/0.48             ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X24 : $i, X25 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.20/0.48          | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 0.20/0.48          | ~ (v8_pre_topc @ X25)
% 0.20/0.48          | ~ (l1_pre_topc @ X25)
% 0.20/0.48          | ~ (v2_pre_topc @ X25)
% 0.20/0.48          | (v2_struct_0 @ X25))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_pcomps_1])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ~ (v8_pre_topc @ sk_A)
% 0.20/0.48        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain, ((v8_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.48        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '40'])).
% 0.20/0.48  thf('42', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (((v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k6_domain_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ X7)
% 0.20/0.48          | (m1_subset_1 @ (k6_domain_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_pre_topc @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k4_waybel_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.20/0.48         ( v1_funct_2 @
% 0.20/0.48           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48         ( m1_subset_1 @
% 0.20/0.48           ( k4_waybel_1 @ A @ B ) @ 
% 0.20/0.48           ( k1_zfmisc_1 @
% 0.20/0.48             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X21 : $i, X22 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X21)
% 0.20/0.48          | (v2_struct_0 @ X21)
% 0.20/0.48          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.20/0.48          | (v1_funct_1 @ (k4_waybel_1 @ X21 @ X22)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.48  thf('53', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf('56', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (![X21 : $i, X22 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X21)
% 0.20/0.48          | (v2_struct_0 @ X21)
% 0.20/0.48          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.20/0.48          | (v1_funct_2 @ (k4_waybel_1 @ X21 @ X22) @ (u1_struct_0 @ X21) @ 
% 0.20/0.48             (u1_struct_0 @ X21)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['55', '58'])).
% 0.20/0.48  thf('60', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (![X21 : $i, X22 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X21)
% 0.20/0.48          | (v2_struct_0 @ X21)
% 0.20/0.48          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.20/0.48          | (m1_subset_1 @ (k4_waybel_1 @ X21 @ X22) @ 
% 0.20/0.48             (k1_zfmisc_1 @ 
% 0.20/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X21)))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ 
% 0.20/0.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48           (k1_zfmisc_1 @ 
% 0.20/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['62', '65'])).
% 0.20/0.48  thf('67', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48           (k1_zfmisc_1 @ 
% 0.20/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.48      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.48  thf(d12_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( l1_pre_topc @ B ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.48                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.48                 ( m1_subset_1 @
% 0.20/0.48                   C @ 
% 0.20/0.48                   ( k1_zfmisc_1 @
% 0.20/0.48                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.48               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.20/0.48                 ( ![D:$i]:
% 0.20/0.48                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.48                     ( ( v4_pre_topc @ D @ B ) =>
% 0.20/0.48                       ( v4_pre_topc @
% 0.20/0.48                         ( k8_relset_1 @
% 0.20/0.48                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.20/0.48                         A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X3)
% 0.20/0.48          | ~ (v5_pre_topc @ X4 @ X5 @ X3)
% 0.20/0.48          | ~ (v4_pre_topc @ X6 @ X3)
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k8_relset_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3) @ X4 @ X6) @ 
% 0.20/0.48             X5)
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48          | ~ (m1_subset_1 @ X4 @ 
% 0.20/0.48               (k1_zfmisc_1 @ 
% 0.20/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))))
% 0.20/0.48          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))
% 0.20/0.48          | ~ (v1_funct_1 @ X4)
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.48          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.48  thf('71', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('72', plain,
% 0.20/0.48      (![X28 : $i]:
% 0.20/0.48         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X28) @ sk_A @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('73', plain, ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.48  thf('74', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.48          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['70', '73'])).
% 0.20/0.48  thf('75', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['74'])).
% 0.20/0.48  thf('76', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['61', '75'])).
% 0.20/0.48  thf('77', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['76'])).
% 0.20/0.48  thf('78', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['54', '77'])).
% 0.20/0.48  thf('79', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['78'])).
% 0.20/0.48  thf('80', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_waybel_9 @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '79'])).
% 0.20/0.48  thf('81', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('82', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.48  thf('83', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | ~ (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | (v4_pre_topc @ 
% 0.20/0.48           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.48           sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['46', '82'])).
% 0.20/0.48  thf('84', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | (v4_pre_topc @ 
% 0.20/0.48           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.48           sk_A)
% 0.20/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '83'])).
% 0.20/0.48  thf('85', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v4_pre_topc @ 
% 0.20/0.48           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.48           sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['84'])).
% 0.20/0.48  thf('86', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf('87', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t7_waybel_9, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.20/0.48         ( l1_orders_2 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( k8_relset_1 @
% 0.20/0.48               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.48               ( k4_waybel_1 @ A @ B ) @ 
% 0.20/0.48               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.20/0.48             ( k6_waybel_0 @ A @ B ) ) ) ) ))).
% 0.20/0.48  thf('88', plain,
% 0.20/0.48      (![X26 : $i, X27 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.20/0.48          | ((k8_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X27) @ 
% 0.20/0.48              (k4_waybel_1 @ X27 @ X26) @ 
% 0.20/0.48              (k6_domain_1 @ (u1_struct_0 @ X27) @ X26))
% 0.20/0.48              = (k6_waybel_0 @ X27 @ X26))
% 0.20/0.48          | ~ (l1_orders_2 @ X27)
% 0.20/0.48          | ~ (v2_lattice3 @ X27)
% 0.20/0.48          | ~ (v5_orders_2 @ X27)
% 0.20/0.48          | ~ (v3_orders_2 @ X27))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_waybel_9])).
% 0.20/0.48  thf('89', plain,
% 0.20/0.48      ((~ (v3_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v2_lattice3 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.48        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.48  thf('90', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('91', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('92', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('93', plain,
% 0.20/0.48      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.48        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.20/0.48  thf('94', plain,
% 0.20/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.48        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['86', '93'])).
% 0.20/0.48  thf('95', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('96', plain,
% 0.20/0.48      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48         (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.20/0.48         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48         = (k6_waybel_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.48  thf('97', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['85', '96'])).
% 0.20/0.48  thf('98', plain, (~ (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('99', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['97', '98'])).
% 0.20/0.48  thf('100', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k6_waybel_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('102', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X16)
% 0.20/0.48          | (v2_struct_0 @ X16)
% 0.20/0.48          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.20/0.48          | (m1_subset_1 @ (k6_waybel_0 @ X16 @ X17) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k6_waybel_0])).
% 0.20/0.48  thf('103', plain,
% 0.20/0.48      (((m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.48  thf('104', plain,
% 0.20/0.48      ((~ (l1_waybel_9 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['100', '103'])).
% 0.20/0.48  thf('105', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('106', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['104', '105'])).
% 0.20/0.48  thf(t5_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.48          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.48  thf('107', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | ~ (v1_xboole_0 @ X2)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.48  thf('108', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.48  thf('109', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['99', '108'])).
% 0.20/0.48  thf('110', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['109'])).
% 0.20/0.48  thf('111', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '110'])).
% 0.20/0.48  thf('112', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('simplify', [status(thm)], ['111'])).
% 0.20/0.48  thf('113', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.20/0.48  thf(cc1_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('114', plain,
% 0.20/0.48      (![X15 : $i]:
% 0.20/0.48         (~ (v1_lattice3 @ X15) | ~ (v2_struct_0 @ X15) | ~ (l1_orders_2 @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.20/0.48  thf('115', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v1_lattice3 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.48  thf('116', plain, ((~ (v1_lattice3 @ sk_A) | ~ (l1_waybel_9 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['112', '115'])).
% 0.20/0.48  thf('117', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('118', plain, ((l1_waybel_9 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('119', plain, ($false),
% 0.20/0.48      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
