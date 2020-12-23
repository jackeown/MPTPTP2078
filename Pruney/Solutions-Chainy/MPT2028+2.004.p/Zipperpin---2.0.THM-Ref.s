%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sSudnuaeTz

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 214 expanded)
%              Number of leaves         :   40 (  80 expanded)
%              Depth                    :   29
%              Number of atoms          : 1282 (3418 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k6_waybel_0_type,type,(
    k6_waybel_0: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( l1_pre_topc @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X19: $i] :
      ( ( l1_pre_topc @ X19 )
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

thf('3',plain,(
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

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t10_pcomps_1])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
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
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X19: $i] :
      ( ( l1_pre_topc @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('16',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('19',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('26',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v5_pre_topc @ X9 @ X10 @ X8 )
      | ~ ( v4_pre_topc @ X11 @ X8 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) @ X9 @ X11 ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X24: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X24 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','47'])).

thf('49',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) @ ( k4_waybel_1 @ X23 @ X22 ) @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) )
        = ( k6_waybel_0 @ X23 @ X22 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_waybel_9])).

thf('57',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k6_waybel_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k6_waybel_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k6_waybel_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k6_waybel_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','64'])).

thf('66',plain,(
    ~ ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('69',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('70',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( k6_waybel_0 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_waybel_0])).

thf('71',plain,
    ( ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('75',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('81',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v4_pre_topc @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ~ ( v4_pre_topc @ ( k6_waybel_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','88'])).

thf('90',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('93',plain,(
    ! [X14: $i] :
      ( ~ ( v1_lattice3 @ X14 )
      | ~ ( v2_struct_0 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['95','96','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sSudnuaeTz
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:08:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 63 iterations in 0.042s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.52  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.22/0.52  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.22/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.22/0.52  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.22/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.52  thf(k6_waybel_0_type, type, k6_waybel_0: $i > $i > $i).
% 0.22/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.22/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.22/0.52  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.22/0.52  thf(dt_l1_waybel_9, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.22/0.52  thf('0', plain, (![X19 : $i]: ((l1_pre_topc @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.52  thf(d1_xboole_0, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf('2', plain, (![X19 : $i]: ((l1_pre_topc @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.52  thf(t27_waybel_9, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.22/0.52         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52           ( ( ![C:$i]:
% 0.22/0.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52                 ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.22/0.52             ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.22/0.52            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52              ( ( ![C:$i]:
% 0.22/0.52                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52                    ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) ) ) =>
% 0.22/0.52                ( v4_pre_topc @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t27_waybel_9])).
% 0.22/0.52  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t10_pcomps_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52           ( ( v8_pre_topc @ A ) =>
% 0.22/0.52             ( v4_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.22/0.52          | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.22/0.52          | ~ (v8_pre_topc @ X21)
% 0.22/0.52          | ~ (l1_pre_topc @ X21)
% 0.22/0.52          | ~ (v2_pre_topc @ X21)
% 0.22/0.52          | (v2_struct_0 @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_pcomps_1])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | ~ (v8_pre_topc @ sk_A)
% 0.22/0.52        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('7', plain, ((v8_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.52        | (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '8'])).
% 0.22/0.52  thf('10', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (((v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k6_domain_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ X12)
% 0.22/0.52          | ~ (m1_subset_1 @ X13 @ X12)
% 0.22/0.52          | (m1_subset_1 @ (k6_domain_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X19 : $i]: ((l1_pre_topc @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.52  thf('17', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k4_waybel_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.22/0.52         ( v1_funct_2 @
% 0.22/0.52           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52         ( m1_subset_1 @
% 0.22/0.52           ( k4_waybel_1 @ A @ B ) @ 
% 0.22/0.52           ( k1_zfmisc_1 @
% 0.22/0.52             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ X17)
% 0.22/0.52          | (v2_struct_0 @ X17)
% 0.22/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.22/0.52          | (v1_funct_1 @ (k4_waybel_1 @ X17 @ X18)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['16', '19'])).
% 0.22/0.52  thf('21', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.52  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ X17)
% 0.22/0.52          | (v2_struct_0 @ X17)
% 0.22/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.22/0.52          | (v1_funct_2 @ (k4_waybel_1 @ X17 @ X18) @ (u1_struct_0 @ X17) @ 
% 0.22/0.52             (u1_struct_0 @ X17)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52         (u1_struct_0 @ sk_A))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52           (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '26'])).
% 0.22/0.52  thf('28', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52           (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.52  thf('31', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ X17)
% 0.22/0.52          | (v2_struct_0 @ X17)
% 0.22/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.22/0.52          | (m1_subset_1 @ (k4_waybel_1 @ X17 @ X18) @ 
% 0.22/0.52             (k1_zfmisc_1 @ 
% 0.22/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17)))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52         (k1_zfmisc_1 @ 
% 0.22/0.52          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['30', '33'])).
% 0.22/0.52  thf('35', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf(d12_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( l1_pre_topc @ B ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.52                 ( m1_subset_1 @
% 0.22/0.52                   C @ 
% 0.22/0.52                   ( k1_zfmisc_1 @
% 0.22/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.52               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.22/0.52                 ( ![D:$i]:
% 0.22/0.52                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.52                     ( ( v4_pre_topc @ D @ B ) =>
% 0.22/0.52                       ( v4_pre_topc @
% 0.22/0.52                         ( k8_relset_1 @
% 0.22/0.52                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.22/0.52                         A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X8)
% 0.22/0.52          | ~ (v5_pre_topc @ X9 @ X10 @ X8)
% 0.22/0.52          | ~ (v4_pre_topc @ X11 @ X8)
% 0.22/0.52          | (v4_pre_topc @ 
% 0.22/0.52             (k8_relset_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ X9 @ X11) @ 
% 0.22/0.52             X10)
% 0.22/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.52          | ~ (m1_subset_1 @ X9 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.22/0.52          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.22/0.52          | ~ (v1_funct_1 @ X9)
% 0.22/0.52          | ~ (l1_pre_topc @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1))
% 0.22/0.52          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v4_pre_topc @ 
% 0.22/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.52             sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B_1) @ sk_A @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X24 : $i]:
% 0.22/0.52         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X24) @ sk_A @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_B_1) @ sk_A @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1))
% 0.22/0.52          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v4_pre_topc @ 
% 0.22/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.52             sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['38', '41'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | (v4_pre_topc @ 
% 0.22/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.52             sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1))
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v4_pre_topc @ 
% 0.22/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.52             sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '43'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | (v4_pre_topc @ 
% 0.22/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.52             sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_B_1))
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v4_pre_topc @ 
% 0.22/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.52             sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | (v4_pre_topc @ 
% 0.22/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.52             sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_waybel_9 @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v4_pre_topc @ 
% 0.22/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.52             sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '47'])).
% 0.22/0.52  thf('49', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v4_pre_topc @ 
% 0.22/0.52             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              (k4_waybel_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.52             sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (v4_pre_topc @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.22/0.52        | (v4_pre_topc @ 
% 0.22/0.52           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.22/0.52           sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '50'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | (v4_pre_topc @ 
% 0.22/0.52           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.22/0.52           sk_A)
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '51'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (v4_pre_topc @ 
% 0.22/0.52           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.22/0.52           sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['52'])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.52  thf('55', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t7_waybel_9, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.22/0.52         ( l1_orders_2 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52           ( ( k8_relset_1 @
% 0.22/0.52               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.52               ( k4_waybel_1 @ A @ B ) @ 
% 0.22/0.52               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.22/0.52             ( k6_waybel_0 @ A @ B ) ) ) ) ))).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.22/0.52          | ((k8_relset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X23) @ 
% 0.22/0.52              (k4_waybel_1 @ X23 @ X22) @ 
% 0.22/0.52              (k6_domain_1 @ (u1_struct_0 @ X23) @ X22))
% 0.22/0.52              = (k6_waybel_0 @ X23 @ X22))
% 0.22/0.52          | ~ (l1_orders_2 @ X23)
% 0.22/0.52          | ~ (v2_lattice3 @ X23)
% 0.22/0.52          | ~ (v5_orders_2 @ X23)
% 0.22/0.52          | ~ (v3_orders_2 @ X23))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_waybel_9])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      ((~ (v3_orders_2 @ sk_A)
% 0.22/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.22/0.52        | ~ (v2_lattice3 @ sk_A)
% 0.22/0.52        | ~ (l1_orders_2 @ sk_A)
% 0.22/0.52        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.22/0.52            = (k6_waybel_0 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.52  thf('58', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('59', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('60', plain, ((v2_lattice3 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      ((~ (l1_orders_2 @ sk_A)
% 0.22/0.52        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.22/0.52            = (k6_waybel_0 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.52        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52            (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.22/0.52            = (k6_waybel_0 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['54', '61'])).
% 0.22/0.52  thf('63', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52         (k4_waybel_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.22/0.52         = (k6_waybel_0 @ sk_A @ sk_B_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['53', '64'])).
% 0.22/0.52  thf('66', plain, (~ (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B_1) @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('67', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['65', '66'])).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.52  thf('69', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k6_waybel_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52       ( m1_subset_1 @
% 0.22/0.52         ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.52  thf('70', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ X15)
% 0.22/0.52          | (v2_struct_0 @ X15)
% 0.22/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.22/0.52          | (m1_subset_1 @ (k6_waybel_0 @ X15 @ X16) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_waybel_0])).
% 0.22/0.52  thf('71', plain,
% 0.22/0.52      (((m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.22/0.52  thf('72', plain,
% 0.22/0.52      ((~ (l1_waybel_9 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['68', '71'])).
% 0.22/0.52  thf('73', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('74', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['72', '73'])).
% 0.22/0.52  thf(t5_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.52  thf('75', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X3 @ X4)
% 0.22/0.52          | ~ (v1_xboole_0 @ X5)
% 0.22/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B_1))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['67', '76'])).
% 0.22/0.52  thf('78', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k6_waybel_0 @ sk_A @ sk_B_1))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['77'])).
% 0.22/0.52  thf('79', plain,
% 0.22/0.52      (((v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '78'])).
% 0.22/0.52  thf('80', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (m1_subset_1 @ (k6_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['72', '73'])).
% 0.22/0.52  thf(cc2_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.22/0.52  thf('81', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.52          | (v4_pre_topc @ X6 @ X7)
% 0.22/0.52          | ~ (v1_xboole_0 @ X6)
% 0.22/0.52          | ~ (l1_pre_topc @ X7)
% 0.22/0.52          | ~ (v2_pre_topc @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.22/0.52  thf('82', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | ~ (v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B_1))
% 0.22/0.52        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B_1) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.22/0.52  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | ~ (v1_xboole_0 @ (k6_waybel_0 @ sk_A @ sk_B_1))
% 0.22/0.52        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B_1) @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['82', '83'])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['79', '84'])).
% 0.22/0.52  thf('86', plain,
% 0.22/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['85'])).
% 0.22/0.52  thf('87', plain, (~ (v4_pre_topc @ (k6_waybel_0 @ sk_A @ sk_B_1) @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('88', plain, (((v2_struct_0 @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['86', '87'])).
% 0.22/0.52  thf('89', plain, ((~ (l1_waybel_9 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '88'])).
% 0.22/0.52  thf('90', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('91', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['89', '90'])).
% 0.22/0.52  thf('92', plain,
% 0.22/0.52      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.22/0.52  thf(cc1_lattice3, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_orders_2 @ A ) =>
% 0.22/0.52       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.22/0.52  thf('93', plain,
% 0.22/0.52      (![X14 : $i]:
% 0.22/0.52         (~ (v1_lattice3 @ X14) | ~ (v2_struct_0 @ X14) | ~ (l1_orders_2 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.22/0.52  thf('94', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_waybel_9 @ X0) | ~ (v2_struct_0 @ X0) | ~ (v1_lattice3 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['92', '93'])).
% 0.22/0.52  thf('95', plain, ((~ (v1_lattice3 @ sk_A) | ~ (l1_waybel_9 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['91', '94'])).
% 0.22/0.52  thf('96', plain, ((v1_lattice3 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('97', plain, ((l1_waybel_9 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('98', plain, ($false),
% 0.22/0.52      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
