%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qTOmt8zbLG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 216 expanded)
%              Number of leaves         :   42 (  81 expanded)
%              Depth                    :   28
%              Number of atoms          : 1326 (3420 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k6_waybel_0_type,type,(
    k6_waybel_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( ( k6_domain_1 @ X10 @ X11 )
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) @ ( k4_waybel_1 @ X23 @ X22 ) @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) )
        = ( k6_waybel_0 @ X23 @ X22 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_waybel_9])).

thf('7',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k6_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X19: $i] :
      ( ( l1_pre_topc @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t10_pcomps_1])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v4_pre_topc @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( v4_pre_topc @ X9 @ X6 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    | ~ ( v4_pre_topc @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','69'])).

thf('71',plain,
    ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ~ ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('78',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( k6_waybel_0 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_waybel_0])).

thf('79',plain,
    ( ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_xboole_0 @ ( k6_waybel_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_waybel_0])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','93'])).

thf('95',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('98',plain,(
    ! [X12: $i] :
      ( ~ ( v1_lattice3 @ X12 )
      | ~ ( v2_struct_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['100','101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qTOmt8zbLG
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:51:09 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 80 iterations in 0.052s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.19/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.19/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.51  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.19/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.51  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.19/0.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.19/0.51  thf(k6_waybel_0_type, type, k6_waybel_0: $i > $i > $i).
% 0.19/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.19/0.51  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.51  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.19/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.51  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.19/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.51  thf(dt_l1_waybel_9, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.19/0.51  thf('0', plain, (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.51  thf(t27_waybel_9, conjecture,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.19/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.19/0.51         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51           ( ( ![C:$i]:
% 0.19/0.51               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51                 ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.19/0.51             ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i]:
% 0.19/0.51        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.19/0.51            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.19/0.51            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.19/0.51          ( ![B:$i]:
% 0.19/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51              ( ( ![C:$i]:
% 0.19/0.51                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51                    ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.19/0.51                ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t27_waybel_9])).
% 0.19/0.51  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i]:
% 0.19/0.51         ((v1_xboole_0 @ X10)
% 0.19/0.51          | ~ (m1_subset_1 @ X11 @ X10)
% 0.19/0.51          | ((k6_domain_1 @ X10 @ X11) = (k1_tarski @ X11)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('4', plain, (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.51  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t7_waybel_9, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.19/0.51         ( l1_orders_2 @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51           ( ( k8_relset_1 @
% 0.19/0.51               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.51               ( k4_waybel_1 @ A @ B ) @ 
% 0.19/0.51               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.19/0.51             ( k6_waybel_0 @ A @ B ) ) ) ) ))).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X22 : $i, X23 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.19/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X23) @ 
% 0.19/0.51              (k4_waybel_1 @ X23 @ X22) @ 
% 0.19/0.51              (k6_domain_1 @ (u1_struct_0 @ X23) @ X22))
% 0.19/0.51              = (k6_waybel_0 @ X23 @ X22))
% 0.19/0.51          | ~ (l1_orders_2 @ X23)
% 0.19/0.51          | ~ (v2_lattice3 @ X23)
% 0.19/0.51          | ~ (v5_orders_2 @ X23)
% 0.19/0.51          | ~ (v3_orders_2 @ X23))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_waybel_9])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      ((~ (v3_orders_2 @ sk_A)
% 0.19/0.51        | ~ (v5_orders_2 @ sk_A)
% 0.19/0.51        | ~ (v2_lattice3 @ sk_A)
% 0.19/0.51        | ~ (l1_orders_2 @ sk_A)
% 0.19/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.51            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('10', plain, ((v2_lattice3 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      ((~ (l1_orders_2 @ sk_A)
% 0.19/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.51            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.51            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.51            = (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['4', '11'])).
% 0.19/0.51  thf('13', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51         (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.51         = (k6_waybel_0 @ sk_A @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51          (k4_waybel_1 @ sk_A @ sk_B) @ (k1_tarski @ sk_B))
% 0.19/0.51          = (k6_waybel_0 @ sk_A @ sk_B))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['3', '14'])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X19 : $i]: ((l1_pre_topc @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.51  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t10_pcomps_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51           ( ( v8_pre_topc @ A ) =>
% 0.19/0.51             ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.19/0.51          | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.19/0.51          | ~ (v8_pre_topc @ X21)
% 0.19/0.51          | ~ (l1_pre_topc @ X21)
% 0.19/0.51          | ~ (v2_pre_topc @ X21)
% 0.19/0.51          | (v2_struct_0 @ X21))),
% 0.19/0.51      inference('cnf', [status(esa)], [t10_pcomps_1])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | ~ (v8_pre_topc @ sk_A)
% 0.19/0.51        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.51  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('22', plain, ((v8_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.51        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['17', '23'])).
% 0.19/0.51  thf('25', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      (((v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      (((v4_pre_topc @ (k1_tarski @ sk_B) @ sk_A)
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup+', [status(thm)], ['16', '26'])).
% 0.19/0.51  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t2_subset, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      (![X4 : $i, X5 : $i]:
% 0.19/0.51         ((r2_hidden @ X4 @ X5)
% 0.19/0.51          | (v1_xboole_0 @ X5)
% 0.19/0.51          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.19/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.51  thf(t63_subset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r2_hidden @ A @ B ) =>
% 0.19/0.51       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((m1_subset_1 @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X1))
% 0.19/0.51          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.19/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X19 : $i]: ((l1_pre_topc @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.51  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(dt_k4_waybel_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.19/0.51         ( v1_funct_2 @
% 0.19/0.51           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.51         ( m1_subset_1 @
% 0.19/0.51           ( k4_waybel_1 @ A @ B ) @ 
% 0.19/0.51           ( k1_zfmisc_1 @
% 0.19/0.51             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X17 : $i, X18 : $i]:
% 0.19/0.51         (~ (l1_orders_2 @ X17)
% 0.19/0.51          | (v2_struct_0 @ X17)
% 0.19/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.19/0.51          | (v1_funct_1 @ (k4_waybel_1 @ X17 @ X18)))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['34', '37'])).
% 0.19/0.51  thf('39', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.51  thf('42', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (![X17 : $i, X18 : $i]:
% 0.19/0.51         (~ (l1_orders_2 @ X17)
% 0.19/0.51          | (v2_struct_0 @ X17)
% 0.19/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.19/0.51          | (v1_funct_2 @ (k4_waybel_1 @ X17 @ X18) @ (u1_struct_0 @ X17) @ 
% 0.19/0.51             (u1_struct_0 @ X17)))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51         (u1_struct_0 @ sk_A))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51           (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['41', '44'])).
% 0.19/0.51  thf('46', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51           (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.51  thf('48', plain,
% 0.19/0.51      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.51  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('50', plain,
% 0.19/0.51      (![X17 : $i, X18 : $i]:
% 0.19/0.51         (~ (l1_orders_2 @ X17)
% 0.19/0.51          | (v2_struct_0 @ X17)
% 0.19/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.19/0.51          | (m1_subset_1 @ (k4_waybel_1 @ X17 @ X18) @ 
% 0.19/0.51             (k1_zfmisc_1 @ 
% 0.19/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17)))))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.19/0.51  thf('51', plain,
% 0.19/0.51      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.51         (k1_zfmisc_1 @ 
% 0.19/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.51  thf('52', plain,
% 0.19/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.51           (k1_zfmisc_1 @ 
% 0.19/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['48', '51'])).
% 0.19/0.51  thf('53', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('54', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.51           (k1_zfmisc_1 @ 
% 0.19/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.51      inference('demod', [status(thm)], ['52', '53'])).
% 0.19/0.51  thf(d12_pre_topc, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( l1_pre_topc @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( l1_pre_topc @ B ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.51                 ( m1_subset_1 @
% 0.19/0.51                   C @ 
% 0.19/0.51                   ( k1_zfmisc_1 @
% 0.19/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.51               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.19/0.51                 ( ![D:$i]:
% 0.19/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.51                     ( ( v4_pre_topc @ D @ B ) =>
% 0.19/0.51                       ( v4_pre_topc @
% 0.19/0.51                         ( k8_relset_1 @
% 0.19/0.51                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.19/0.51                         A ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X6)
% 0.19/0.51          | ~ (v5_pre_topc @ X7 @ X8 @ X6)
% 0.19/0.51          | ~ (v4_pre_topc @ X9 @ X6)
% 0.19/0.51          | (v4_pre_topc @ 
% 0.19/0.51             (k8_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7 @ X9) @ 
% 0.19/0.51             X8)
% 0.19/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.19/0.51          | ~ (m1_subset_1 @ X7 @ 
% 0.19/0.51               (k1_zfmisc_1 @ 
% 0.19/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.19/0.51          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.19/0.51          | ~ (v1_funct_1 @ X7)
% 0.19/0.51          | ~ (l1_pre_topc @ X8))),
% 0.19/0.51      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.19/0.51  thf('56', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.51          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.51               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | (v4_pre_topc @ 
% 0.19/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.51             sk_A)
% 0.19/0.51          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.19/0.51  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('58', plain,
% 0.19/0.51      (![X24 : $i]:
% 0.19/0.51         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X24) @ sk_A @ sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('59', plain, ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 0.19/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.51  thf('60', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.51          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.51               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | (v4_pre_topc @ 
% 0.19/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.51             sk_A)
% 0.19/0.51          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['56', '59'])).
% 0.19/0.51  thf('61', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (v4_pre_topc @ 
% 0.19/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.51             sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B) @ 
% 0.19/0.51               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.19/0.51          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('simplify', [status(thm)], ['60'])).
% 0.19/0.51  thf('62', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ sk_A)
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | (v4_pre_topc @ 
% 0.19/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.51             sk_A)
% 0.19/0.51          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['47', '61'])).
% 0.19/0.51  thf('63', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (v4_pre_topc @ 
% 0.19/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.51             sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B))
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('simplify', [status(thm)], ['62'])).
% 0.19/0.51  thf('64', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ sk_A)
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | (v4_pre_topc @ 
% 0.19/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.51             sk_A)
% 0.19/0.51          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['40', '63'])).
% 0.19/0.51  thf('65', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (v4_pre_topc @ 
% 0.19/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.51             sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('simplify', [status(thm)], ['64'])).
% 0.19/0.51  thf('66', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (l1_waybel_9 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | (v4_pre_topc @ 
% 0.19/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.51             sk_A)
% 0.19/0.51          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['33', '65'])).
% 0.19/0.51  thf('67', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('68', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51          | (v4_pre_topc @ 
% 0.19/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51              (k4_waybel_1 @ sk_A @ sk_B) @ X0) @ 
% 0.19/0.51             sk_A)
% 0.19/0.51          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['66', '67'])).
% 0.19/0.51  thf('69', plain,
% 0.19/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | ~ (v4_pre_topc @ (k1_tarski @ sk_B) @ sk_A)
% 0.19/0.51        | (v4_pre_topc @ 
% 0.19/0.51           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ (k1_tarski @ sk_B)) @ 
% 0.19/0.51           sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['32', '68'])).
% 0.19/0.51  thf('70', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | (v4_pre_topc @ 
% 0.19/0.51           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51            (k4_waybel_1 @ sk_A @ sk_B) @ (k1_tarski @ sk_B)) @ 
% 0.19/0.51           sk_A)
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['27', '69'])).
% 0.19/0.51  thf('71', plain,
% 0.19/0.51      (((v4_pre_topc @ 
% 0.19/0.51         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51          (k4_waybel_1 @ sk_A @ sk_B) @ (k1_tarski @ sk_B)) @ 
% 0.19/0.51         sk_A)
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('simplify', [status(thm)], ['70'])).
% 0.19/0.51  thf('72', plain,
% 0.19/0.51      (((v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['15', '71'])).
% 0.19/0.51  thf('73', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A))),
% 0.19/0.51      inference('simplify', [status(thm)], ['72'])).
% 0.19/0.51  thf('74', plain, (~ (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('75', plain,
% 0.19/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('clc', [status(thm)], ['73', '74'])).
% 0.19/0.51  thf('76', plain,
% 0.19/0.51      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.51  thf('77', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(dt_k6_waybel_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51       ( m1_subset_1 @
% 0.19/0.51         ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.51  thf('78', plain,
% 0.19/0.51      (![X13 : $i, X14 : $i]:
% 0.19/0.51         (~ (l1_orders_2 @ X13)
% 0.19/0.51          | (v2_struct_0 @ X13)
% 0.19/0.51          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.19/0.51          | (m1_subset_1 @ (k6_waybel_0 @ X13 @ X14) @ 
% 0.19/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k6_waybel_0])).
% 0.19/0.51  thf('79', plain,
% 0.19/0.51      (((m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.19/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['77', '78'])).
% 0.19/0.51  thf('80', plain,
% 0.19/0.51      ((~ (l1_waybel_9 @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.19/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['76', '79'])).
% 0.19/0.51  thf('81', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('82', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B) @ 
% 0.19/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.51      inference('demod', [status(thm)], ['80', '81'])).
% 0.19/0.51  thf(cc1_subset_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.19/0.51  thf('83', plain,
% 0.19/0.51      (![X2 : $i, X3 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.19/0.51          | (v1_xboole_0 @ X2)
% 0.19/0.51          | ~ (v1_xboole_0 @ X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.19/0.51  thf('84', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | (v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['82', '83'])).
% 0.19/0.51  thf('85', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['75', '84'])).
% 0.19/0.51  thf('86', plain,
% 0.19/0.51      (((v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('simplify', [status(thm)], ['85'])).
% 0.19/0.51  thf('87', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(fc9_waybel_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.51         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51       ( ( ~( v1_xboole_0 @ ( k6_waybel_0 @ A @ B ) ) ) & 
% 0.19/0.51         ( v2_waybel_0 @ ( k6_waybel_0 @ A @ B ) @ A ) ) ))).
% 0.19/0.51  thf('88', plain,
% 0.19/0.51      (![X15 : $i, X16 : $i]:
% 0.19/0.51         (~ (l1_orders_2 @ X15)
% 0.19/0.51          | ~ (v3_orders_2 @ X15)
% 0.19/0.51          | (v2_struct_0 @ X15)
% 0.19/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.19/0.51          | ~ (v1_xboole_0 @ (k6_waybel_0 @ X15 @ X16)))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc9_waybel_0])).
% 0.19/0.51  thf('89', plain,
% 0.19/0.51      ((~ (v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v3_orders_2 @ sk_A)
% 0.19/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['87', '88'])).
% 0.19/0.51  thf('90', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('91', plain,
% 0.19/0.51      ((~ (v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['89', '90'])).
% 0.19/0.51  thf('92', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A) | ~ (l1_orders_2 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['86', '91'])).
% 0.19/0.51  thf('93', plain, ((~ (l1_orders_2 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('simplify', [status(thm)], ['92'])).
% 0.19/0.51  thf('94', plain, ((~ (l1_waybel_9 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['0', '93'])).
% 0.19/0.51  thf('95', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('96', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('demod', [status(thm)], ['94', '95'])).
% 0.19/0.51  thf('97', plain,
% 0.19/0.51      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.19/0.51  thf(cc1_lattice3, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( l1_orders_2 @ A ) =>
% 0.19/0.51       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.19/0.51  thf('98', plain,
% 0.19/0.51      (![X12 : $i]:
% 0.19/0.51         (~ (v1_lattice3 @ X12) | ~ (v2_struct_0 @ X12) | ~ (l1_orders_2 @ X12))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.19/0.51  thf('99', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v1_lattice3 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['97', '98'])).
% 0.19/0.51  thf('100', plain, ((~ (v1_lattice3 @ sk_A) | ~ (l1_waybel_9 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['96', '99'])).
% 0.19/0.51  thf('101', plain, ((v1_lattice3 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('102', plain, ((l1_waybel_9 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('103', plain, ($false),
% 0.19/0.51      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
