%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6LbT7Y7RhP

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:23 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  321 (2741 expanded)
%              Number of leaves         :   50 ( 803 expanded)
%              Depth                    :   67
%              Number of atoms          : 3206 (44842 expanded)
%              Number of equality atoms :   90 ( 858 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v19_lattices_type,type,(
    v19_lattices: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_lattice3_type,type,(
    k4_lattice3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_lattice3_type,type,(
    k2_lattice3: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v18_lattices_type,type,(
    v18_lattices: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k8_filter_1_type,type,(
    k8_filter_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(k1_domain_1_type,type,(
    k1_domain_1: $i > $i > $i > $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(t7_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_lattices @ A @ B @ C )
              <=> ( r3_orders_2 @ ( k3_lattice3 @ A ) @ ( k4_lattice3 @ A @ B ) @ ( k4_lattice3 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r3_lattices @ A @ B @ C )
                <=> ( r3_orders_2 @ ( k3_lattice3 @ A ) @ ( k4_lattice3 @ A @ B ) @ ( k4_lattice3 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ C @ A )
        & ( m1_subset_1 @ D @ B ) )
     => ( ( k1_domain_1 @ A @ B @ C @ D )
        = ( k4_tarski @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( ( k1_domain_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k4_tarski @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_domain_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B_1 @ X0 )
        = ( k4_tarski @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C )
      = ( k4_tarski @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,
    ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C )
      = ( k4_tarski @ sk_B_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) )
    | ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
   <= ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_filter_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k8_filter_1 @ A ) )
              <=> ( r3_lattices @ A @ B @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r3_lattices @ X19 @ X18 @ X20 )
      | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X19 ) @ X18 @ X20 ) @ ( k8_filter_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t32_filter_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k8_filter_1 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k8_filter_1 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
    | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C ) @ ( k8_filter_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C ) @ ( k8_filter_1 @ sk_A ) )
    | ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C ) @ ( k8_filter_1 @ sk_A ) )
   <= ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C ) @ ( k8_filter_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['6','19'])).

thf(dt_k3_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ( v1_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v3_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v4_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v5_orders_2 @ ( k3_lattice3 @ A ) )
        & ( l1_orders_2 @ ( k3_lattice3 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('22',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('23',plain,(
    ! [X25: $i] :
      ( ( v1_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ~ ( v1_orders_2 @ X2 )
      | ( X2
        = ( g1_orders_2 @ ( u1_struct_0 @ X2 ) @ ( u1_orders_2 @ X2 ) ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(redefinition_k2_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ( k2_lattice3 @ A )
        = ( k8_filter_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X29: $i] :
      ( ( ( k2_lattice3 @ X29 )
        = ( k8_filter_1 @ X29 ) )
      | ~ ( l3_lattices @ X29 )
      | ~ ( v10_lattices @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_lattice3])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k2_lattice3 @ sk_A )
      = ( k8_filter_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_lattice3 @ sk_A )
    = ( k8_filter_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(dt_k2_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ( v1_partfun1 @ ( k2_lattice3 @ A ) @ ( u1_struct_0 @ A ) )
        & ( v1_relat_2 @ ( k2_lattice3 @ A ) )
        & ( v4_relat_2 @ ( k2_lattice3 @ A ) )
        & ( v8_relat_2 @ ( k2_lattice3 @ A ) )
        & ( m1_subset_1 @ ( k2_lattice3 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( k2_lattice3 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( l3_lattices @ X24 )
      | ~ ( v10_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattice3])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k8_filter_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k8_filter_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( k8_filter_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( g1_orders_2 @ X8 @ X9 )
       != ( g1_orders_2 @ X6 @ X7 ) )
      | ( X9 = X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_filter_1 @ sk_A )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( k8_filter_1 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_lattice3 @ sk_A )
    = ( k8_filter_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(d2_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ( k3_lattice3 @ A )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k2_lattice3 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X21: $i] :
      ( ( ( k3_lattice3 @ X21 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X21 ) @ ( k2_lattice3 @ X21 ) ) )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_lattice3])).

thf('42',plain,
    ( ( ( k3_lattice3 @ sk_A )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( k8_filter_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k3_lattice3 @ sk_A )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( k8_filter_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k3_lattice3 @ sk_A )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_filter_1 @ sk_A )
        = X0 )
      | ( ( k3_lattice3 @ sk_A )
       != ( g1_orders_2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattice3 @ sk_A )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( ( k8_filter_1 @ sk_A )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','48'])).

thf('50',plain,
    ( ( ( k8_filter_1 @ sk_A )
      = ( u1_orders_2 @ ( k3_lattice3 @ sk_A ) ) )
    | ~ ( v1_orders_2 @ ( k3_lattice3 @ sk_A ) )
    | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
    | ( ( k8_filter_1 @ sk_A )
      = ( u1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','50'])).

thf('52',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
    | ( ( k8_filter_1 @ sk_A )
      = ( u1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k8_filter_1 @ sk_A )
      = ( u1_orders_2 @ ( k3_lattice3 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k8_filter_1 @ sk_A )
      = ( u1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','56'])).

thf('58',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_filter_1 @ sk_A )
      = ( u1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( u1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( u1_orders_2 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k8_filter_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X25: $i] :
      ( ( v1_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('66',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('67',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( u1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('68',plain,(
    ! [X2: $i] :
      ( ~ ( v1_orders_2 @ X2 )
      | ( X2
        = ( g1_orders_2 @ ( u1_struct_0 @ X2 ) @ ( u1_orders_2 @ X2 ) ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('69',plain,
    ( ( ( k3_lattice3 @ sk_A )
      = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) @ ( k8_filter_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
    | ~ ( v1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v1_orders_2 @ ( k3_lattice3 @ sk_A ) )
    | ( ( k3_lattice3 @ sk_A )
      = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_orders_2 @ ( k3_lattice3 @ sk_A ) )
    | ( ( k3_lattice3 @ sk_A )
      = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k3_lattice3 @ sk_A )
      = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) @ ( k8_filter_1 @ sk_A ) ) )
    | ~ ( v1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattice3 @ sk_A )
      = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','75'])).

thf('77',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattice3 @ sk_A )
      = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k3_lattice3 @ sk_A )
    = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k8_filter_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('83',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( g1_orders_2 @ X8 @ X9 )
       != ( g1_orders_2 @ X6 @ X7 ) )
      | ( X8 = X6 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( k8_filter_1 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k3_lattice3 @ sk_A )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = X0 )
      | ( ( k3_lattice3 @ sk_A )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k3_lattice3 @ sk_A )
     != ( k3_lattice3 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k8_filter_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','90'])).

thf('92',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) )
    | ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) )
    | ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattice3 @ A @ B )
            = B ) ) ) )).

thf('104',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( ( k4_lattice3 @ X23 @ X22 )
        = X22 )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattice3 @ sk_A @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattice3 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k4_lattice3 @ sk_A @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) )
   <= ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['7'])).

thf('112',plain,
    ( ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ sk_C )
   <= ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( ( k4_lattice3 @ X23 @ X22 )
        = X22 )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattice3 @ sk_A @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattice3 @ sk_A @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k4_lattice3 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
   <= ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('124',plain,(
    ! [X25: $i] :
      ( ( v3_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('125',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('126',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( r3_orders_2 @ X15 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','133'])).

thf('135',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ sk_C )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ sk_C )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['122','138'])).

thf('140',plain,
    ( ( ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) ) )
   <= ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('146',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('147',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( u1_orders_2 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ ( k3_lattice3 @ sk_A ) ) )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('150',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( u1_orders_2 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k8_filter_1 @ sk_A ) )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k8_filter_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k8_filter_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C ) @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['144','155'])).

thf('157',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C ) @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C ) @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) ) )
   <= ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C )
      = ( k4_tarski @ sk_B_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('163',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X19 ) @ X18 @ X20 ) @ ( k8_filter_1 @ X19 ) )
      | ( r3_lattices @ X19 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t32_filter_1])).

thf('164',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C ) @ ( k8_filter_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C ) @ ( k8_filter_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','165','166','167','168'])).

thf('170',plain,
    ( ( ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','169'])).

thf('171',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
   <= ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['101'])).

thf('172',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) ) )
   <= ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf(fc4_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ~ ( v2_struct_0 @ ( k3_lattice3 @ A ) )
        & ( v1_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v3_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v4_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v5_orders_2 @ ( k3_lattice3 @ A ) ) ) ) )).

thf('175',plain,(
    ! [X28: $i] :
      ( ~ ( v2_struct_0 @ ( k3_lattice3 @ X28 ) )
      | ~ ( l3_lattices @ X28 )
      | ~ ( v10_lattices @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc4_lattice3])).

thf('176',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) )
   <= ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['179','180'])).

thf(rc14_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ? [B: $i] :
          ( ( v19_lattices @ B @ A )
          & ( v18_lattices @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('182',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc14_lattices])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['181','184'])).

thf('186',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
   <= ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X17 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc14_lattices])).

thf('192',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) )
   <= ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( r3_lattices @ sk_A @ sk_B_1 @ sk_C )
    | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['7'])).

thf('199',plain,(
    r3_lattices @ sk_A @ sk_B_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['102','197','198'])).

thf('200',plain,
    ( ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['100','199'])).

thf('201',plain,(
    ! [X25: $i] :
      ( ( v3_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('202',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('203',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X25: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('205',plain,(
    ! [X25: $i] :
      ( ( v1_orders_2 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('206',plain,(
    ! [X2: $i] :
      ( ~ ( v1_orders_2 @ X2 )
      | ( X2
        = ( g1_orders_2 @ ( u1_struct_0 @ X2 ) @ ( u1_orders_2 @ X2 ) ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('207',plain,(
    ! [X21: $i] :
      ( ( ( k3_lattice3 @ X21 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X21 ) @ ( k2_lattice3 @ X21 ) ) )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_lattice3])).

thf('208',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( k2_lattice3 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( l3_lattices @ X24 )
      | ~ ( v10_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattice3])).

thf('209',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( g1_orders_2 @ X8 @ X9 )
       != ( g1_orders_2 @ X6 @ X7 ) )
      | ( X8 = X6 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('210',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k2_lattice3 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_lattice3 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['207','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k3_lattice3 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_lattice3 @ X1 )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( ( u1_struct_0 @ X1 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['206','212'])).

thf('214',plain,(
    ! [X1: $i] :
      ( ( ( u1_struct_0 @ X1 )
        = ( u1_struct_0 @ ( k3_lattice3 @ X1 ) ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_orders_2 @ ( k3_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k3_lattice3 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['205','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k3_lattice3 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k3_lattice3 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['204','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k3_lattice3 @ X0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k3_lattice3 @ X0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('220',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r3_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( r1_orders_2 @ X15 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('221',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k3_lattice3 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_lattice3 @ X0 ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ X0 ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ X0 ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ X0 ) @ X2 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['218','221'])).

thf('223',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ X0 ) @ X2 @ X1 )
      | ( r3_orders_2 @ ( k3_lattice3 @ X0 ) @ X2 @ X1 )
      | ( v2_struct_0 @ ( k3_lattice3 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['203','223'])).

thf('225',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['202','227'])).

thf('229',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['201','232'])).

thf('234',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['233','234','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['200','237'])).

thf('239',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['238','239'])).

thf('241',plain,
    ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) )
   <= ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['101'])).

thf('242',plain,
    ( ( k4_lattice3 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['118','119'])).

thf('243',plain,
    ( ( k4_lattice3 @ sk_A @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['108','109'])).

thf('244',plain,
    ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C )
   <= ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,(
    ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ ( k4_lattice3 @ sk_A @ sk_B_1 ) @ ( k4_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['102','197'])).

thf('246',plain,(
    ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['244','245'])).

thf('247',plain,
    ( ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['240','246'])).

thf('248',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k3_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X28: $i] :
      ( ~ ( v2_struct_0 @ ( k3_lattice3 @ X28 ) )
      | ~ ( l3_lattices @ X28 )
      | ~ ( v10_lattices @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc4_lattice3])).

thf('251',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('258',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['258','259','260'])).

thf('262',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v1_xboole_0 @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X17 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc14_lattices])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,(
    $false ),
    inference(demod,[status(thm)],['0','268'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6LbT7Y7RhP
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:18 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 331 iterations in 0.191s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.47/0.65  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.47/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.65  thf(v19_lattices_type, type, v19_lattices: $i > $i > $o).
% 0.47/0.65  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(k4_lattice3_type, type, k4_lattice3: $i > $i > $i).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.65  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.47/0.65  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.47/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.65  thf(k2_lattice3_type, type, k2_lattice3: $i > $i).
% 0.47/0.65  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.47/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.65  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.47/0.65  thf(v18_lattices_type, type, v18_lattices: $i > $i > $o).
% 0.47/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.65  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.47/0.65  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.47/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.65  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.47/0.65  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.47/0.65  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.47/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.65  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.47/0.65  thf(k8_filter_1_type, type, k8_filter_1: $i > $i).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.47/0.65  thf(k1_domain_1_type, type, k1_domain_1: $i > $i > $i > $i > $i).
% 0.47/0.65  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.47/0.65  thf(t7_lattice3, conjecture,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.65               ( ( r3_lattices @ A @ B @ C ) <=>
% 0.47/0.65                 ( r3_orders_2 @
% 0.47/0.65                   ( k3_lattice3 @ A ) @ ( k4_lattice3 @ A @ B ) @ 
% 0.47/0.65                   ( k4_lattice3 @ A @ C ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]:
% 0.47/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.47/0.65            ( l3_lattices @ A ) ) =>
% 0.47/0.65          ( ![B:$i]:
% 0.47/0.65            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.65              ( ![C:$i]:
% 0.47/0.65                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.65                  ( ( r3_lattices @ A @ B @ C ) <=>
% 0.47/0.65                    ( r3_orders_2 @
% 0.47/0.65                      ( k3_lattice3 @ A ) @ ( k4_lattice3 @ A @ B ) @ 
% 0.47/0.65                      ( k4_lattice3 @ A @ C ) ) ) ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t7_lattice3])).
% 0.47/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(redefinition_k1_domain_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.47/0.65         ( m1_subset_1 @ C @ A ) & ( m1_subset_1 @ D @ B ) ) =>
% 0.47/0.65       ( ( k1_domain_1 @ A @ B @ C @ D ) = ( k4_tarski @ C @ D ) ) ))).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X10 @ X11)
% 0.47/0.65          | (v1_xboole_0 @ X12)
% 0.47/0.65          | (v1_xboole_0 @ X11)
% 0.47/0.65          | ~ (m1_subset_1 @ X13 @ X12)
% 0.47/0.65          | ((k1_domain_1 @ X11 @ X12 @ X10 @ X13) = (k4_tarski @ X10 @ X13)))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k1_domain_1])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k1_domain_1 @ (u1_struct_0 @ sk_A) @ X1 @ sk_B_1 @ X0)
% 0.47/0.65            = (k4_tarski @ sk_B_1 @ X0))
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ X1)
% 0.47/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.65          | (v1_xboole_0 @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.65        | ((k1_domain_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65            sk_B_1 @ sk_C) = (k4_tarski @ sk_B_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['1', '4'])).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      ((((k1_domain_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.47/0.65          sk_C) = (k4_tarski @ sk_B_1 @ sk_C))
% 0.47/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ (k4_lattice3 @ sk_A @ sk_B_1) @ 
% 0.47/0.65         (k4_lattice3 @ sk_A @ sk_C))
% 0.47/0.65        | (r3_lattices @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      (((r3_lattices @ sk_A @ sk_B_1 @ sk_C))
% 0.47/0.65         <= (((r3_lattices @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.65      inference('split', [status(esa)], ['7'])).
% 0.47/0.65  thf('9', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('10', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t32_filter_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.65               ( ( r2_hidden @
% 0.47/0.65                   ( k1_domain_1 @
% 0.47/0.65                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.47/0.65                   ( k8_filter_1 @ A ) ) <=>
% 0.47/0.65                 ( r3_lattices @ A @ B @ C ) ) ) ) ) ) ))).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.47/0.65          | ~ (r3_lattices @ X19 @ X18 @ X20)
% 0.47/0.65          | (r2_hidden @ 
% 0.47/0.65             (k1_domain_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X19) @ X18 @ 
% 0.47/0.65              X20) @ 
% 0.47/0.65             (k8_filter_1 @ X19))
% 0.47/0.65          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.47/0.65          | ~ (l3_lattices @ X19)
% 0.47/0.65          | ~ (v10_lattices @ X19)
% 0.47/0.65          | (v2_struct_0 @ X19))),
% 0.47/0.65      inference('cnf', [status(esa)], [t32_filter_1])).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_A)
% 0.47/0.65          | ~ (v10_lattices @ sk_A)
% 0.47/0.65          | ~ (l3_lattices @ sk_A)
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.65          | (r2_hidden @ 
% 0.47/0.65             (k1_domain_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65              sk_B_1 @ X0) @ 
% 0.47/0.65             (k8_filter_1 @ sk_A))
% 0.47/0.65          | ~ (r3_lattices @ sk_A @ sk_B_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.65  thf('13', plain, ((v10_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('14', plain, ((l3_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_A)
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.65          | (r2_hidden @ 
% 0.47/0.65             (k1_domain_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65              sk_B_1 @ X0) @ 
% 0.47/0.65             (k8_filter_1 @ sk_A))
% 0.47/0.65          | ~ (r3_lattices @ sk_A @ sk_B_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      ((~ (r3_lattices @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.65        | (r2_hidden @ 
% 0.47/0.65           (k1_domain_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65            sk_B_1 @ sk_C) @ 
% 0.47/0.65           (k8_filter_1 @ sk_A))
% 0.47/0.65        | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['9', '15'])).
% 0.47/0.65  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('18', plain,
% 0.47/0.65      (((r2_hidden @ 
% 0.47/0.65         (k1_domain_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.47/0.65          sk_C) @ 
% 0.47/0.65         (k8_filter_1 @ sk_A))
% 0.47/0.65        | ~ (r3_lattices @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.65      inference('clc', [status(thm)], ['16', '17'])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (((r2_hidden @ 
% 0.47/0.65         (k1_domain_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.47/0.65          sk_C) @ 
% 0.47/0.65         (k8_filter_1 @ sk_A))) <= (((r3_lattices @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['8', '18'])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      ((((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C) @ (k8_filter_1 @ sk_A))
% 0.47/0.65         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.65         <= (((r3_lattices @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['6', '19'])).
% 0.47/0.65  thf(dt_k3_lattice3, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.47/0.65       ( ( v1_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.47/0.65         ( v3_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.47/0.65         ( v4_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.47/0.65         ( v5_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.47/0.65         ( l1_orders_2 @ ( k3_lattice3 @ A ) ) ) ))).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (![X25 : $i]:
% 0.47/0.65         ((l1_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.65          | ~ (l3_lattices @ X25)
% 0.47/0.65          | ~ (v10_lattices @ X25)
% 0.47/0.65          | (v2_struct_0 @ X25))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      (![X25 : $i]:
% 0.47/0.65         ((l1_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.65          | ~ (l3_lattices @ X25)
% 0.47/0.65          | ~ (v10_lattices @ X25)
% 0.47/0.65          | (v2_struct_0 @ X25))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X25 : $i]:
% 0.47/0.65         ((v1_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.65          | ~ (l3_lattices @ X25)
% 0.47/0.65          | ~ (v10_lattices @ X25)
% 0.47/0.65          | (v2_struct_0 @ X25))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.65  thf(abstractness_v1_orders_2, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_orders_2 @ A ) =>
% 0.47/0.65       ( ( v1_orders_2 @ A ) =>
% 0.47/0.65         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X2 : $i]:
% 0.47/0.65         (~ (v1_orders_2 @ X2)
% 0.47/0.65          | ((X2) = (g1_orders_2 @ (u1_struct_0 @ X2) @ (u1_orders_2 @ X2)))
% 0.47/0.65          | ~ (l1_orders_2 @ X2))),
% 0.47/0.65      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.47/0.65  thf(redefinition_k2_lattice3, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.47/0.65       ( ( k2_lattice3 @ A ) = ( k8_filter_1 @ A ) ) ))).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (![X29 : $i]:
% 0.47/0.65         (((k2_lattice3 @ X29) = (k8_filter_1 @ X29))
% 0.47/0.65          | ~ (l3_lattices @ X29)
% 0.47/0.65          | ~ (v10_lattices @ X29)
% 0.47/0.65          | (v2_struct_0 @ X29))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k2_lattice3])).
% 0.47/0.65  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      ((~ (v10_lattices @ sk_A)
% 0.47/0.65        | ~ (l3_lattices @ sk_A)
% 0.47/0.65        | ((k2_lattice3 @ sk_A) = (k8_filter_1 @ sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('28', plain, ((v10_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('29', plain, ((l3_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('30', plain, (((k2_lattice3 @ sk_A) = (k8_filter_1 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.47/0.65  thf(dt_k2_lattice3, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.47/0.65       ( ( v1_partfun1 @ ( k2_lattice3 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.47/0.65         ( v1_relat_2 @ ( k2_lattice3 @ A ) ) & 
% 0.47/0.65         ( v4_relat_2 @ ( k2_lattice3 @ A ) ) & 
% 0.47/0.65         ( v8_relat_2 @ ( k2_lattice3 @ A ) ) & 
% 0.47/0.65         ( m1_subset_1 @
% 0.47/0.65           ( k2_lattice3 @ A ) @ 
% 0.47/0.65           ( k1_zfmisc_1 @
% 0.47/0.65             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.65  thf('31', plain,
% 0.47/0.65      (![X24 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (k2_lattice3 @ X24) @ 
% 0.47/0.65           (k1_zfmisc_1 @ 
% 0.47/0.65            (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X24))))
% 0.47/0.65          | ~ (l3_lattices @ X24)
% 0.47/0.65          | ~ (v10_lattices @ X24)
% 0.47/0.65          | (v2_struct_0 @ X24))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_lattice3])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (((m1_subset_1 @ (k8_filter_1 @ sk_A) @ 
% 0.47/0.65         (k1_zfmisc_1 @ 
% 0.47/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.47/0.65        | (v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v10_lattices @ sk_A)
% 0.47/0.65        | ~ (l3_lattices @ sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['30', '31'])).
% 0.47/0.65  thf('33', plain, ((v10_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('34', plain, ((l3_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (((m1_subset_1 @ (k8_filter_1 @ sk_A) @ 
% 0.47/0.65         (k1_zfmisc_1 @ 
% 0.47/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.47/0.65        | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.47/0.65  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('37', plain,
% 0.47/0.65      ((m1_subset_1 @ (k8_filter_1 @ sk_A) @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.47/0.65      inference('clc', [status(thm)], ['35', '36'])).
% 0.47/0.65  thf(free_g1_orders_2, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.47/0.65       ( ![C:$i,D:$i]:
% 0.47/0.65         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.47/0.65           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.47/0.65  thf('38', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         (((g1_orders_2 @ X8 @ X9) != (g1_orders_2 @ X6 @ X7))
% 0.47/0.65          | ((X9) = (X7))
% 0.47/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8))))),
% 0.47/0.65      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.47/0.65  thf('39', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k8_filter_1 @ sk_A) = (X0))
% 0.47/0.65          | ((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (k8_filter_1 @ sk_A))
% 0.47/0.65              != (g1_orders_2 @ X1 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.65  thf('40', plain, (((k2_lattice3 @ sk_A) = (k8_filter_1 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.47/0.65  thf(d2_lattice3, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.47/0.65       ( ( k3_lattice3 @ A ) =
% 0.47/0.65         ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k2_lattice3 @ A ) ) ) ))).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      (![X21 : $i]:
% 0.47/0.65         (((k3_lattice3 @ X21)
% 0.47/0.65            = (g1_orders_2 @ (u1_struct_0 @ X21) @ (k2_lattice3 @ X21)))
% 0.47/0.65          | ~ (l3_lattices @ X21)
% 0.47/0.65          | ~ (v10_lattices @ X21)
% 0.47/0.65          | (v2_struct_0 @ X21))),
% 0.47/0.65      inference('cnf', [status(esa)], [d2_lattice3])).
% 0.47/0.65  thf('42', plain,
% 0.47/0.65      ((((k3_lattice3 @ sk_A)
% 0.47/0.65          = (g1_orders_2 @ (u1_struct_0 @ sk_A) @ (k8_filter_1 @ sk_A)))
% 0.47/0.65        | (v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v10_lattices @ sk_A)
% 0.47/0.65        | ~ (l3_lattices @ sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['40', '41'])).
% 0.47/0.65  thf('43', plain, ((v10_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('44', plain, ((l3_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('45', plain,
% 0.47/0.65      ((((k3_lattice3 @ sk_A)
% 0.47/0.65          = (g1_orders_2 @ (u1_struct_0 @ sk_A) @ (k8_filter_1 @ sk_A)))
% 0.47/0.65        | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.47/0.65  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('47', plain,
% 0.47/0.65      (((k3_lattice3 @ sk_A)
% 0.47/0.65         = (g1_orders_2 @ (u1_struct_0 @ sk_A) @ (k8_filter_1 @ sk_A)))),
% 0.47/0.65      inference('clc', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('48', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k8_filter_1 @ sk_A) = (X0))
% 0.47/0.65          | ((k3_lattice3 @ sk_A) != (g1_orders_2 @ X1 @ X0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['39', '47'])).
% 0.47/0.65  thf('49', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k3_lattice3 @ sk_A) != (X0))
% 0.47/0.65          | ~ (l1_orders_2 @ X0)
% 0.47/0.65          | ~ (v1_orders_2 @ X0)
% 0.47/0.65          | ((k8_filter_1 @ sk_A) = (u1_orders_2 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['24', '48'])).
% 0.47/0.65  thf('50', plain,
% 0.47/0.65      ((((k8_filter_1 @ sk_A) = (u1_orders_2 @ (k3_lattice3 @ sk_A)))
% 0.47/0.65        | ~ (v1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.65        | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['49'])).
% 0.47/0.65  thf('51', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v10_lattices @ sk_A)
% 0.47/0.65        | ~ (l3_lattices @ sk_A)
% 0.47/0.65        | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.65        | ((k8_filter_1 @ sk_A) = (u1_orders_2 @ (k3_lattice3 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['23', '50'])).
% 0.47/0.65  thf('52', plain, ((v10_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('53', plain, ((l3_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('54', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.65        | ((k8_filter_1 @ sk_A) = (u1_orders_2 @ (k3_lattice3 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.47/0.65  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      ((((k8_filter_1 @ sk_A) = (u1_orders_2 @ (k3_lattice3 @ sk_A)))
% 0.47/0.65        | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.65      inference('clc', [status(thm)], ['54', '55'])).
% 0.47/0.65  thf('57', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v10_lattices @ sk_A)
% 0.47/0.65        | ~ (l3_lattices @ sk_A)
% 0.47/0.65        | ((k8_filter_1 @ sk_A) = (u1_orders_2 @ (k3_lattice3 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['22', '56'])).
% 0.47/0.65  thf('58', plain, ((v10_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('59', plain, ((l3_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('60', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ((k8_filter_1 @ sk_A) = (u1_orders_2 @ (k3_lattice3 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.47/0.65  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('62', plain,
% 0.47/0.65      (((k8_filter_1 @ sk_A) = (u1_orders_2 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.65      inference('clc', [status(thm)], ['60', '61'])).
% 0.47/0.65  thf(d9_orders_2, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_orders_2 @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.65               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.47/0.65                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf('63', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.47/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (u1_orders_2 @ X4))
% 0.47/0.65          | (r1_orders_2 @ X4 @ X3 @ X5)
% 0.47/0.65          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.47/0.65          | ~ (l1_orders_2 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.47/0.65  thf('64', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k8_filter_1 @ sk_A))
% 0.47/0.65          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_A)))
% 0.47/0.65          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X1 @ X0)
% 0.47/0.65          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.65  thf('65', plain,
% 0.47/0.65      (![X25 : $i]:
% 0.47/0.65         ((v1_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.65          | ~ (l3_lattices @ X25)
% 0.47/0.65          | ~ (v10_lattices @ X25)
% 0.47/0.65          | (v2_struct_0 @ X25))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.65  thf('66', plain,
% 0.47/0.65      (![X25 : $i]:
% 0.47/0.65         ((l1_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.65          | ~ (l3_lattices @ X25)
% 0.47/0.65          | ~ (v10_lattices @ X25)
% 0.47/0.65          | (v2_struct_0 @ X25))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.65  thf('67', plain,
% 0.47/0.65      (((k8_filter_1 @ sk_A) = (u1_orders_2 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.65      inference('clc', [status(thm)], ['60', '61'])).
% 0.47/0.65  thf('68', plain,
% 0.47/0.65      (![X2 : $i]:
% 0.47/0.65         (~ (v1_orders_2 @ X2)
% 0.47/0.65          | ((X2) = (g1_orders_2 @ (u1_struct_0 @ X2) @ (u1_orders_2 @ X2)))
% 0.47/0.65          | ~ (l1_orders_2 @ X2))),
% 0.47/0.65      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.47/0.65  thf('69', plain,
% 0.47/0.65      ((((k3_lattice3 @ sk_A)
% 0.47/0.65          = (g1_orders_2 @ (u1_struct_0 @ (k3_lattice3 @ sk_A)) @ 
% 0.47/0.65             (k8_filter_1 @ sk_A)))
% 0.47/0.65        | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.65        | ~ (v1_orders_2 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['67', '68'])).
% 0.47/0.65  thf('70', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v10_lattices @ sk_A)
% 0.47/0.65        | ~ (l3_lattices @ sk_A)
% 0.47/0.65        | ~ (v1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.65        | ((k3_lattice3 @ sk_A)
% 0.47/0.65            = (g1_orders_2 @ (u1_struct_0 @ (k3_lattice3 @ sk_A)) @ 
% 0.47/0.65               (k8_filter_1 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['66', '69'])).
% 0.47/0.65  thf('71', plain, ((v10_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('72', plain, ((l3_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('73', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.65        | ((k3_lattice3 @ sk_A)
% 0.47/0.65            = (g1_orders_2 @ (u1_struct_0 @ (k3_lattice3 @ sk_A)) @ 
% 0.47/0.65               (k8_filter_1 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.47/0.65  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('75', plain,
% 0.47/0.65      ((((k3_lattice3 @ sk_A)
% 0.47/0.65          = (g1_orders_2 @ (u1_struct_0 @ (k3_lattice3 @ sk_A)) @ 
% 0.47/0.65             (k8_filter_1 @ sk_A)))
% 0.47/0.65        | ~ (v1_orders_2 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.65      inference('clc', [status(thm)], ['73', '74'])).
% 0.47/0.65  thf('76', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v10_lattices @ sk_A)
% 0.47/0.65        | ~ (l3_lattices @ sk_A)
% 0.47/0.65        | ((k3_lattice3 @ sk_A)
% 0.47/0.65            = (g1_orders_2 @ (u1_struct_0 @ (k3_lattice3 @ sk_A)) @ 
% 0.47/0.65               (k8_filter_1 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['65', '75'])).
% 0.47/0.65  thf('77', plain, ((v10_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('78', plain, ((l3_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('79', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ((k3_lattice3 @ sk_A)
% 0.47/0.65            = (g1_orders_2 @ (u1_struct_0 @ (k3_lattice3 @ sk_A)) @ 
% 0.47/0.65               (k8_filter_1 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.47/0.65  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('81', plain,
% 0.47/0.65      (((k3_lattice3 @ sk_A)
% 0.47/0.65         = (g1_orders_2 @ (u1_struct_0 @ (k3_lattice3 @ sk_A)) @ 
% 0.47/0.65            (k8_filter_1 @ sk_A)))),
% 0.47/0.65      inference('clc', [status(thm)], ['79', '80'])).
% 0.47/0.65  thf('82', plain,
% 0.47/0.65      ((m1_subset_1 @ (k8_filter_1 @ sk_A) @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.47/0.65      inference('clc', [status(thm)], ['35', '36'])).
% 0.47/0.65  thf('83', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         (((g1_orders_2 @ X8 @ X9) != (g1_orders_2 @ X6 @ X7))
% 0.47/0.65          | ((X8) = (X6))
% 0.47/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8))))),
% 0.47/0.65      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.47/0.65  thf('84', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((u1_struct_0 @ sk_A) = (X0))
% 0.47/0.65          | ((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (k8_filter_1 @ sk_A))
% 0.47/0.65              != (g1_orders_2 @ X0 @ X1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['82', '83'])).
% 0.47/0.65  thf('85', plain,
% 0.47/0.65      (((k3_lattice3 @ sk_A)
% 0.47/0.65         = (g1_orders_2 @ (u1_struct_0 @ sk_A) @ (k8_filter_1 @ sk_A)))),
% 0.47/0.65      inference('clc', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('86', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((u1_struct_0 @ sk_A) = (X0))
% 0.47/0.65          | ((k3_lattice3 @ sk_A) != (g1_orders_2 @ X0 @ X1)))),
% 0.47/0.65      inference('demod', [status(thm)], ['84', '85'])).
% 0.47/0.65  thf('87', plain,
% 0.47/0.65      ((((k3_lattice3 @ sk_A) != (k3_lattice3 @ sk_A))
% 0.47/0.65        | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ (k3_lattice3 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['81', '86'])).
% 0.47/0.65  thf('88', plain,
% 0.47/0.65      (((u1_struct_0 @ sk_A) = (u1_struct_0 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['87'])).
% 0.47/0.65  thf('89', plain,
% 0.47/0.65      (((u1_struct_0 @ sk_A) = (u1_struct_0 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['87'])).
% 0.47/0.65  thf('90', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k8_filter_1 @ sk_A))
% 0.47/0.65          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.65          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X1 @ X0)
% 0.47/0.65          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['64', '88', '89'])).
% 0.47/0.65  thf('91', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_A)
% 0.47/0.65          | ~ (v10_lattices @ sk_A)
% 0.47/0.65          | ~ (l3_lattices @ sk_A)
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.65          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.65          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.47/0.65          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ (k8_filter_1 @ sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['21', '90'])).
% 0.47/0.65  thf('92', plain, ((v10_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('93', plain, ((l3_lattices @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('94', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_A)
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.65          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.65          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.47/0.65          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ (k8_filter_1 @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.47/0.65  thf('95', plain,
% 0.47/0.65      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.65         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.65         | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C)
% 0.47/0.65         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.65         | (v2_struct_0 @ sk_A))) <= (((r3_lattices @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['20', '94'])).
% 0.47/0.65  thf('96', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('97', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('98', plain,
% 0.47/0.65      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.65         | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C)
% 0.47/0.65         | (v2_struct_0 @ sk_A))) <= (((r3_lattices @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.65      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.47/0.65  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('100', plain,
% 0.47/0.65      ((((r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C)
% 0.47/0.65         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.65         <= (((r3_lattices @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.65      inference('clc', [status(thm)], ['98', '99'])).
% 0.47/0.65  thf('101', plain,
% 0.47/0.65      ((~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.65           (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))
% 0.47/0.65        | ~ (r3_lattices @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('102', plain,
% 0.47/0.65      (~
% 0.47/0.65       ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ (k4_lattice3 @ sk_A @ sk_B_1) @ 
% 0.47/0.65         (k4_lattice3 @ sk_A @ sk_C))) | 
% 0.47/0.65       ~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.65      inference('split', [status(esa)], ['101'])).
% 0.47/0.65  thf('103', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d3_lattice3, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.65           ( ( k4_lattice3 @ A @ B ) = ( B ) ) ) ) ))).
% 0.47/0.65  thf('104', plain,
% 0.47/0.65      (![X22 : $i, X23 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.47/0.65          | ((k4_lattice3 @ X23 @ X22) = (X22))
% 0.47/0.65          | ~ (l3_lattices @ X23)
% 0.47/0.65          | ~ (v10_lattices @ X23)
% 0.47/0.65          | (v2_struct_0 @ X23))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_lattice3])).
% 0.47/0.65  thf('105', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v10_lattices @ sk_A)
% 0.47/0.66        | ~ (l3_lattices @ sk_A)
% 0.47/0.66        | ((k4_lattice3 @ sk_A @ sk_C) = (sk_C)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['103', '104'])).
% 0.47/0.66  thf('106', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('107', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('108', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A) | ((k4_lattice3 @ sk_A @ sk_C) = (sk_C)))),
% 0.47/0.66      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.47/0.66  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('110', plain, (((k4_lattice3 @ sk_A @ sk_C) = (sk_C))),
% 0.47/0.66      inference('clc', [status(thm)], ['108', '109'])).
% 0.47/0.66  thf('111', plain,
% 0.47/0.66      (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ (k4_lattice3 @ sk_A @ sk_B_1) @ 
% 0.47/0.66         (k4_lattice3 @ sk_A @ sk_C)))
% 0.47/0.66         <= (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('split', [status(esa)], ['7'])).
% 0.47/0.66  thf('112', plain,
% 0.47/0.66      (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ (k4_lattice3 @ sk_A @ sk_B_1) @ 
% 0.47/0.66         sk_C))
% 0.47/0.66         <= (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['110', '111'])).
% 0.47/0.66  thf('113', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('114', plain,
% 0.47/0.66      (![X22 : $i, X23 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.47/0.66          | ((k4_lattice3 @ X23 @ X22) = (X22))
% 0.47/0.66          | ~ (l3_lattices @ X23)
% 0.47/0.66          | ~ (v10_lattices @ X23)
% 0.47/0.66          | (v2_struct_0 @ X23))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_lattice3])).
% 0.47/0.66  thf('115', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | ~ (v10_lattices @ sk_A)
% 0.47/0.66        | ~ (l3_lattices @ sk_A)
% 0.47/0.66        | ((k4_lattice3 @ sk_A @ sk_B_1) = (sk_B_1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['113', '114'])).
% 0.47/0.66  thf('116', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('117', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('118', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A) | ((k4_lattice3 @ sk_A @ sk_B_1) = (sk_B_1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.47/0.66  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('120', plain, (((k4_lattice3 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.47/0.66      inference('clc', [status(thm)], ['118', '119'])).
% 0.47/0.66  thf('121', plain,
% 0.47/0.66      (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C))
% 0.47/0.66         <= (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('demod', [status(thm)], ['112', '120'])).
% 0.47/0.66  thf('122', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('123', plain,
% 0.47/0.66      (![X25 : $i]:
% 0.47/0.66         ((l1_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.66          | ~ (l3_lattices @ X25)
% 0.47/0.66          | ~ (v10_lattices @ X25)
% 0.47/0.66          | (v2_struct_0 @ X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.66  thf('124', plain,
% 0.47/0.66      (![X25 : $i]:
% 0.47/0.66         ((v3_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.66          | ~ (l3_lattices @ X25)
% 0.47/0.66          | ~ (v10_lattices @ X25)
% 0.47/0.66          | (v2_struct_0 @ X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.66  thf('125', plain,
% 0.47/0.66      (((u1_struct_0 @ sk_A) = (u1_struct_0 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['87'])).
% 0.47/0.66  thf(redefinition_r3_orders_2, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.47/0.66         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.47/0.66         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.47/0.66  thf('126', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.47/0.66          | ~ (l1_orders_2 @ X15)
% 0.47/0.66          | ~ (v3_orders_2 @ X15)
% 0.47/0.66          | (v2_struct_0 @ X15)
% 0.47/0.66          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.47/0.66          | (r1_orders_2 @ X15 @ X14 @ X16)
% 0.47/0.66          | ~ (r3_orders_2 @ X15 @ X14 @ X16))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.47/0.66  thf('127', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.66          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_A)))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['125', '126'])).
% 0.47/0.66  thf('128', plain,
% 0.47/0.66      (((u1_struct_0 @ sk_A) = (u1_struct_0 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['87'])).
% 0.47/0.66  thf('129', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.66          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['127', '128'])).
% 0.47/0.66  thf('130', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (v10_lattices @ sk_A)
% 0.47/0.66          | ~ (l3_lattices @ sk_A)
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X1 @ X0)
% 0.47/0.66          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ X1 @ X0)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['124', '129'])).
% 0.47/0.66  thf('131', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('132', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('133', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X1 @ X0)
% 0.47/0.66          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ X1 @ X0)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.47/0.66  thf('134', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (v10_lattices @ sk_A)
% 0.47/0.66          | ~ (l3_lattices @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.66          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['123', '133'])).
% 0.47/0.66  thf('135', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('136', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('137', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.66          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.47/0.66  thf('138', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.66          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify', [status(thm)], ['137'])).
% 0.47/0.66  thf('139', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ sk_C)
% 0.47/0.66          | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ sk_C)
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['122', '138'])).
% 0.47/0.66  thf('140', plain,
% 0.47/0.66      ((((v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66         | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C)
% 0.47/0.66         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66         | (v2_struct_0 @ sk_A)))
% 0.47/0.66         <= (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['121', '139'])).
% 0.47/0.66  thf('141', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('142', plain,
% 0.47/0.66      ((((v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66         | (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C)
% 0.47/0.66         | (v2_struct_0 @ sk_A)))
% 0.47/0.66         <= (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('demod', [status(thm)], ['140', '141'])).
% 0.47/0.66  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('144', plain,
% 0.47/0.66      ((((r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C)
% 0.47/0.66         | (v2_struct_0 @ (k3_lattice3 @ sk_A))))
% 0.47/0.66         <= (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('clc', [status(thm)], ['142', '143'])).
% 0.47/0.66  thf('145', plain,
% 0.47/0.66      (![X25 : $i]:
% 0.47/0.66         ((l1_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.66          | ~ (l3_lattices @ X25)
% 0.47/0.66          | ~ (v10_lattices @ X25)
% 0.47/0.66          | (v2_struct_0 @ X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.66  thf('146', plain,
% 0.47/0.66      (((u1_struct_0 @ sk_A) = (u1_struct_0 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['87'])).
% 0.47/0.66  thf('147', plain,
% 0.47/0.66      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.47/0.66          | ~ (r1_orders_2 @ X4 @ X3 @ X5)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ (u1_orders_2 @ X4))
% 0.47/0.66          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.47/0.66          | ~ (l1_orders_2 @ X4))),
% 0.47/0.66      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.47/0.66  thf('148', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_A)))
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.47/0.66             (u1_orders_2 @ (k3_lattice3 @ sk_A)))
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['146', '147'])).
% 0.47/0.66  thf('149', plain,
% 0.47/0.66      (((u1_struct_0 @ sk_A) = (u1_struct_0 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['87'])).
% 0.47/0.66  thf('150', plain,
% 0.47/0.66      (((k8_filter_1 @ sk_A) = (u1_orders_2 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.66      inference('clc', [status(thm)], ['60', '61'])).
% 0.47/0.66  thf('151', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X0 @ X1) @ (k8_filter_1 @ sk_A))
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X0 @ X1))),
% 0.47/0.66      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.47/0.66  thf('152', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (v10_lattices @ sk_A)
% 0.47/0.66          | ~ (l3_lattices @ sk_A)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X1 @ X0)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k8_filter_1 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['145', '151'])).
% 0.47/0.66  thf('153', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('154', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('155', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ X1 @ X0)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k8_filter_1 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['152', '153', '154'])).
% 0.47/0.66  thf('156', plain,
% 0.47/0.66      ((((v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.66         | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C) @ (k8_filter_1 @ sk_A))
% 0.47/0.66         | (v2_struct_0 @ sk_A)))
% 0.47/0.66         <= (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['144', '155'])).
% 0.47/0.66  thf('157', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('158', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('159', plain,
% 0.47/0.66      ((((v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66         | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C) @ (k8_filter_1 @ sk_A))
% 0.47/0.66         | (v2_struct_0 @ sk_A)))
% 0.47/0.66         <= (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('demod', [status(thm)], ['156', '157', '158'])).
% 0.47/0.66  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('161', plain,
% 0.47/0.66      ((((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C) @ (k8_filter_1 @ sk_A))
% 0.47/0.66         | (v2_struct_0 @ (k3_lattice3 @ sk_A))))
% 0.47/0.66         <= (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('clc', [status(thm)], ['159', '160'])).
% 0.47/0.66  thf('162', plain,
% 0.47/0.66      ((((k1_domain_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.47/0.66          sk_C) = (k4_tarski @ sk_B_1 @ sk_C))
% 0.47/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.66  thf('163', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.47/0.66          | ~ (r2_hidden @ 
% 0.47/0.66               (k1_domain_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X19) @ 
% 0.47/0.66                X18 @ X20) @ 
% 0.47/0.66               (k8_filter_1 @ X19))
% 0.47/0.66          | (r3_lattices @ X19 @ X18 @ X20)
% 0.47/0.66          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.47/0.66          | ~ (l3_lattices @ X19)
% 0.47/0.66          | ~ (v10_lattices @ X19)
% 0.47/0.66          | (v2_struct_0 @ X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t32_filter_1])).
% 0.47/0.66  thf('164', plain,
% 0.47/0.66      ((~ (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C) @ (k8_filter_1 @ sk_A))
% 0.47/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | ~ (v10_lattices @ sk_A)
% 0.47/0.66        | ~ (l3_lattices @ sk_A)
% 0.47/0.66        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | (r3_lattices @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.66        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['162', '163'])).
% 0.47/0.66  thf('165', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('166', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('167', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('168', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('169', plain,
% 0.47/0.66      ((~ (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C) @ (k8_filter_1 @ sk_A))
% 0.47/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | (r3_lattices @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.66      inference('demod', [status(thm)], ['164', '165', '166', '167', '168'])).
% 0.47/0.66  thf('170', plain,
% 0.47/0.66      ((((v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66         | (r3_lattices @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.66         | (v2_struct_0 @ sk_A)
% 0.47/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.66         <= (((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['161', '169'])).
% 0.47/0.66  thf('171', plain,
% 0.47/0.66      ((~ (r3_lattices @ sk_A @ sk_B_1 @ sk_C))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.66      inference('split', [status(esa)], ['101'])).
% 0.47/0.66  thf('172', plain,
% 0.47/0.66      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66         | (v2_struct_0 @ sk_A)
% 0.47/0.66         | (v2_struct_0 @ (k3_lattice3 @ sk_A))))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['170', '171'])).
% 0.47/0.66  thf('173', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('174', plain,
% 0.47/0.66      ((((v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('clc', [status(thm)], ['172', '173'])).
% 0.47/0.66  thf(fc4_lattice3, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.47/0.66       ( ( ~( v2_struct_0 @ ( k3_lattice3 @ A ) ) ) & 
% 0.47/0.66         ( v1_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.47/0.66         ( v3_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.47/0.66         ( v4_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.47/0.66         ( v5_orders_2 @ ( k3_lattice3 @ A ) ) ) ))).
% 0.47/0.66  thf('175', plain,
% 0.47/0.66      (![X28 : $i]:
% 0.47/0.66         (~ (v2_struct_0 @ (k3_lattice3 @ X28))
% 0.47/0.66          | ~ (l3_lattices @ X28)
% 0.47/0.66          | ~ (v10_lattices @ X28)
% 0.47/0.66          | (v2_struct_0 @ X28))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc4_lattice3])).
% 0.47/0.66  thf('176', plain,
% 0.47/0.66      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66         | (v2_struct_0 @ sk_A)
% 0.47/0.66         | ~ (v10_lattices @ sk_A)
% 0.47/0.66         | ~ (l3_lattices @ sk_A)))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['174', '175'])).
% 0.47/0.66  thf('177', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('178', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('179', plain,
% 0.47/0.66      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('demod', [status(thm)], ['176', '177', '178'])).
% 0.47/0.66  thf('180', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('181', plain,
% 0.47/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('clc', [status(thm)], ['179', '180'])).
% 0.47/0.66  thf(rc14_lattices, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.47/0.66       ( ?[B:$i]:
% 0.47/0.66         ( ( v19_lattices @ B @ A ) & ( v18_lattices @ B @ A ) & 
% 0.47/0.66           ( ~( v1_xboole_0 @ B ) ) & 
% 0.47/0.66           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.66  thf('182', plain,
% 0.47/0.66      (![X17 : $i]:
% 0.47/0.66         ((m1_subset_1 @ (sk_B @ X17) @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.66          | ~ (l3_lattices @ X17)
% 0.47/0.66          | ~ (v10_lattices @ X17)
% 0.47/0.66          | (v2_struct_0 @ X17))),
% 0.47/0.66      inference('cnf', [status(esa)], [rc14_lattices])).
% 0.47/0.66  thf(cc1_subset_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_xboole_0 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.47/0.66  thf('183', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.47/0.66          | (v1_xboole_0 @ X0)
% 0.47/0.66          | ~ (v1_xboole_0 @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.47/0.66  thf('184', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.47/0.66          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['182', '183'])).
% 0.47/0.66  thf('185', plain,
% 0.47/0.66      ((((v1_xboole_0 @ (sk_B @ sk_A))
% 0.47/0.66         | ~ (l3_lattices @ sk_A)
% 0.47/0.66         | ~ (v10_lattices @ sk_A)
% 0.47/0.66         | (v2_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['181', '184'])).
% 0.47/0.66  thf('186', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('187', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('188', plain,
% 0.47/0.66      ((((v1_xboole_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.47/0.66  thf('189', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('190', plain,
% 0.47/0.66      (((v1_xboole_0 @ (sk_B @ sk_A)))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('clc', [status(thm)], ['188', '189'])).
% 0.47/0.66  thf('191', plain,
% 0.47/0.66      (![X17 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ (sk_B @ X17))
% 0.47/0.66          | ~ (l3_lattices @ X17)
% 0.47/0.66          | ~ (v10_lattices @ X17)
% 0.47/0.66          | (v2_struct_0 @ X17))),
% 0.47/0.66      inference('cnf', [status(esa)], [rc14_lattices])).
% 0.47/0.66  thf('192', plain,
% 0.47/0.66      ((((v2_struct_0 @ sk_A)
% 0.47/0.66         | ~ (v10_lattices @ sk_A)
% 0.47/0.66         | ~ (l3_lattices @ sk_A)))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['190', '191'])).
% 0.47/0.66  thf('193', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('194', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('195', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A))
% 0.47/0.66         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('demod', [status(thm)], ['192', '193', '194'])).
% 0.47/0.66  thf('196', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('197', plain,
% 0.47/0.66      (((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.47/0.66       ~
% 0.47/0.66       ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ (k4_lattice3 @ sk_A @ sk_B_1) @ 
% 0.47/0.66         (k4_lattice3 @ sk_A @ sk_C)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['195', '196'])).
% 0.47/0.66  thf('198', plain,
% 0.47/0.66      (((r3_lattices @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.47/0.66       ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ (k4_lattice3 @ sk_A @ sk_B_1) @ 
% 0.47/0.66         (k4_lattice3 @ sk_A @ sk_C)))),
% 0.47/0.66      inference('split', [status(esa)], ['7'])).
% 0.47/0.66  thf('199', plain, (((r3_lattices @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['102', '197', '198'])).
% 0.47/0.66  thf('200', plain,
% 0.47/0.66      (((r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C)
% 0.47/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['100', '199'])).
% 0.47/0.66  thf('201', plain,
% 0.47/0.66      (![X25 : $i]:
% 0.47/0.66         ((v3_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.66          | ~ (l3_lattices @ X25)
% 0.47/0.66          | ~ (v10_lattices @ X25)
% 0.47/0.66          | (v2_struct_0 @ X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.66  thf('202', plain,
% 0.47/0.66      (![X25 : $i]:
% 0.47/0.66         ((l1_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.66          | ~ (l3_lattices @ X25)
% 0.47/0.66          | ~ (v10_lattices @ X25)
% 0.47/0.66          | (v2_struct_0 @ X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.66  thf('203', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('204', plain,
% 0.47/0.66      (![X25 : $i]:
% 0.47/0.66         ((l1_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.66          | ~ (l3_lattices @ X25)
% 0.47/0.66          | ~ (v10_lattices @ X25)
% 0.47/0.66          | (v2_struct_0 @ X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.66  thf('205', plain,
% 0.47/0.66      (![X25 : $i]:
% 0.47/0.66         ((v1_orders_2 @ (k3_lattice3 @ X25))
% 0.47/0.66          | ~ (l3_lattices @ X25)
% 0.47/0.66          | ~ (v10_lattices @ X25)
% 0.47/0.66          | (v2_struct_0 @ X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.47/0.66  thf('206', plain,
% 0.47/0.66      (![X2 : $i]:
% 0.47/0.66         (~ (v1_orders_2 @ X2)
% 0.47/0.66          | ((X2) = (g1_orders_2 @ (u1_struct_0 @ X2) @ (u1_orders_2 @ X2)))
% 0.47/0.66          | ~ (l1_orders_2 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.47/0.66  thf('207', plain,
% 0.47/0.66      (![X21 : $i]:
% 0.47/0.66         (((k3_lattice3 @ X21)
% 0.47/0.66            = (g1_orders_2 @ (u1_struct_0 @ X21) @ (k2_lattice3 @ X21)))
% 0.47/0.66          | ~ (l3_lattices @ X21)
% 0.47/0.66          | ~ (v10_lattices @ X21)
% 0.47/0.66          | (v2_struct_0 @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [d2_lattice3])).
% 0.47/0.66  thf('208', plain,
% 0.47/0.66      (![X24 : $i]:
% 0.47/0.66         ((m1_subset_1 @ (k2_lattice3 @ X24) @ 
% 0.47/0.66           (k1_zfmisc_1 @ 
% 0.47/0.66            (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X24))))
% 0.47/0.66          | ~ (l3_lattices @ X24)
% 0.47/0.66          | ~ (v10_lattices @ X24)
% 0.47/0.66          | (v2_struct_0 @ X24))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k2_lattice3])).
% 0.47/0.66  thf('209', plain,
% 0.47/0.66      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.66         (((g1_orders_2 @ X8 @ X9) != (g1_orders_2 @ X6 @ X7))
% 0.47/0.66          | ((X8) = (X6))
% 0.47/0.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8))))),
% 0.47/0.66      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.47/0.66  thf('210', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ((u1_struct_0 @ X0) = (X1))
% 0.47/0.66          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (k2_lattice3 @ X0))
% 0.47/0.66              != (g1_orders_2 @ X1 @ X2)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['208', '209'])).
% 0.47/0.66  thf('211', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (((k3_lattice3 @ X0) != (g1_orders_2 @ X2 @ X1))
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ((u1_struct_0 @ X0) = (X2))
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['207', '210'])).
% 0.47/0.66  thf('212', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (((u1_struct_0 @ X0) = (X2))
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ((k3_lattice3 @ X0) != (g1_orders_2 @ X2 @ X1)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['211'])).
% 0.47/0.66  thf('213', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k3_lattice3 @ X1) != (X0))
% 0.47/0.66          | ~ (l1_orders_2 @ X0)
% 0.47/0.66          | ~ (v1_orders_2 @ X0)
% 0.47/0.66          | (v2_struct_0 @ X1)
% 0.47/0.66          | ~ (v10_lattices @ X1)
% 0.47/0.66          | ~ (l3_lattices @ X1)
% 0.47/0.66          | ((u1_struct_0 @ X1) = (u1_struct_0 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['206', '212'])).
% 0.47/0.66  thf('214', plain,
% 0.47/0.66      (![X1 : $i]:
% 0.47/0.66         (((u1_struct_0 @ X1) = (u1_struct_0 @ (k3_lattice3 @ X1)))
% 0.47/0.66          | ~ (l3_lattices @ X1)
% 0.47/0.66          | ~ (v10_lattices @ X1)
% 0.47/0.66          | (v2_struct_0 @ X1)
% 0.47/0.66          | ~ (v1_orders_2 @ (k3_lattice3 @ X1))
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ X1)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['213'])).
% 0.47/0.66  thf('215', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ X0))
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ((u1_struct_0 @ X0) = (u1_struct_0 @ (k3_lattice3 @ X0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['205', '214'])).
% 0.47/0.66  thf('216', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((u1_struct_0 @ X0) = (u1_struct_0 @ (k3_lattice3 @ X0)))
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ X0))
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['215'])).
% 0.47/0.66  thf('217', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ((u1_struct_0 @ X0) = (u1_struct_0 @ (k3_lattice3 @ X0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['204', '216'])).
% 0.47/0.66  thf('218', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((u1_struct_0 @ X0) = (u1_struct_0 @ (k3_lattice3 @ X0)))
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['217'])).
% 0.47/0.66  thf('219', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((u1_struct_0 @ X0) = (u1_struct_0 @ (k3_lattice3 @ X0)))
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['217'])).
% 0.47/0.66  thf('220', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.47/0.66          | ~ (l1_orders_2 @ X15)
% 0.47/0.66          | ~ (v3_orders_2 @ X15)
% 0.47/0.66          | (v2_struct_0 @ X15)
% 0.47/0.66          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.47/0.66          | (r3_orders_2 @ X15 @ X14 @ X16)
% 0.47/0.66          | ~ (r1_orders_2 @ X15 @ X14 @ X16))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.47/0.66  thf('221', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ X0) @ X1 @ X2)
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ X0) @ X1 @ X2)
% 0.47/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_lattice3 @ X0)))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ X0))
% 0.47/0.66          | ~ (v3_orders_2 @ (k3_lattice3 @ X0))
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['219', '220'])).
% 0.47/0.66  thf('222', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ X0))
% 0.47/0.66          | ~ (v3_orders_2 @ (k3_lattice3 @ X0))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ X0))
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ X0) @ X2 @ X1)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ X0) @ X2 @ X1)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['218', '221'])).
% 0.47/0.66  thf('223', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ X0) @ X2 @ X1)
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ X0) @ X2 @ X1)
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ X0))
% 0.47/0.66          | ~ (v3_orders_2 @ (k3_lattice3 @ X0))
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ X0))
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['222'])).
% 0.47/0.66  thf('224', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (v10_lattices @ sk_A)
% 0.47/0.66          | ~ (l3_lattices @ sk_A)
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['203', '223'])).
% 0.47/0.66  thf('225', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('226', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('227', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['224', '225', '226'])).
% 0.47/0.66  thf('228', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (v10_lattices @ sk_A)
% 0.47/0.66          | ~ (l3_lattices @ sk_A)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['202', '227'])).
% 0.47/0.66  thf('229', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('230', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('231', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['228', '229', '230'])).
% 0.47/0.66  thf('232', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify', [status(thm)], ['231'])).
% 0.47/0.66  thf('233', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (v10_lattices @ sk_A)
% 0.47/0.66          | ~ (l3_lattices @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['201', '232'])).
% 0.47/0.66  thf('234', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('235', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('236', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['233', '234', '235'])).
% 0.47/0.66  thf('237', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66          | (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify', [status(thm)], ['236'])).
% 0.47/0.66  thf('238', plain,
% 0.47/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C)
% 0.47/0.66        | (v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['200', '237'])).
% 0.47/0.66  thf('239', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('240', plain,
% 0.47/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C)
% 0.47/0.66        | (v2_struct_0 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['238', '239'])).
% 0.47/0.66  thf('241', plain,
% 0.47/0.66      ((~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66           (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C)))
% 0.47/0.66         <= (~
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('split', [status(esa)], ['101'])).
% 0.47/0.66  thf('242', plain, (((k4_lattice3 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.47/0.66      inference('clc', [status(thm)], ['118', '119'])).
% 0.47/0.66  thf('243', plain, (((k4_lattice3 @ sk_A @ sk_C) = (sk_C))),
% 0.47/0.66      inference('clc', [status(thm)], ['108', '109'])).
% 0.47/0.66  thf('244', plain,
% 0.47/0.66      ((~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C))
% 0.47/0.66         <= (~
% 0.47/0.66             ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ 
% 0.47/0.66               (k4_lattice3 @ sk_A @ sk_B_1) @ (k4_lattice3 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('demod', [status(thm)], ['241', '242', '243'])).
% 0.47/0.66  thf('245', plain,
% 0.47/0.66      (~
% 0.47/0.66       ((r3_orders_2 @ (k3_lattice3 @ sk_A) @ (k4_lattice3 @ sk_A @ sk_B_1) @ 
% 0.47/0.66         (k4_lattice3 @ sk_A @ sk_C)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['102', '197'])).
% 0.47/0.66  thf('246', plain, (~ (r3_orders_2 @ (k3_lattice3 @ sk_A) @ sk_B_1 @ sk_C)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['244', '245'])).
% 0.47/0.66  thf('247', plain,
% 0.47/0.66      (((v2_struct_0 @ (k3_lattice3 @ sk_A))
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['240', '246'])).
% 0.47/0.66  thf('248', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('249', plain,
% 0.47/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | (v2_struct_0 @ (k3_lattice3 @ sk_A)))),
% 0.47/0.66      inference('clc', [status(thm)], ['247', '248'])).
% 0.47/0.66  thf('250', plain,
% 0.47/0.66      (![X28 : $i]:
% 0.47/0.66         (~ (v2_struct_0 @ (k3_lattice3 @ X28))
% 0.47/0.66          | ~ (l3_lattices @ X28)
% 0.47/0.66          | ~ (v10_lattices @ X28)
% 0.47/0.66          | (v2_struct_0 @ X28))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc4_lattice3])).
% 0.47/0.66  thf('251', plain,
% 0.47/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | ~ (v10_lattices @ sk_A)
% 0.47/0.66        | ~ (l3_lattices @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['249', '250'])).
% 0.47/0.66  thf('252', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('253', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('254', plain,
% 0.47/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['251', '252', '253'])).
% 0.47/0.66  thf('255', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('256', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('clc', [status(thm)], ['254', '255'])).
% 0.47/0.66  thf('257', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v10_lattices @ X0)
% 0.47/0.66          | ~ (l3_lattices @ X0)
% 0.47/0.66          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.47/0.66          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['182', '183'])).
% 0.47/0.66  thf('258', plain,
% 0.47/0.66      (((v1_xboole_0 @ (sk_B @ sk_A))
% 0.47/0.66        | ~ (l3_lattices @ sk_A)
% 0.47/0.66        | ~ (v10_lattices @ sk_A)
% 0.47/0.66        | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['256', '257'])).
% 0.47/0.66  thf('259', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('260', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('261', plain, (((v1_xboole_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['258', '259', '260'])).
% 0.47/0.66  thf('262', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('263', plain, ((v1_xboole_0 @ (sk_B @ sk_A))),
% 0.47/0.66      inference('clc', [status(thm)], ['261', '262'])).
% 0.47/0.66  thf('264', plain,
% 0.47/0.66      (![X17 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ (sk_B @ X17))
% 0.47/0.66          | ~ (l3_lattices @ X17)
% 0.47/0.66          | ~ (v10_lattices @ X17)
% 0.47/0.66          | (v2_struct_0 @ X17))),
% 0.47/0.66      inference('cnf', [status(esa)], [rc14_lattices])).
% 0.47/0.66  thf('265', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A) | ~ (v10_lattices @ sk_A) | ~ (l3_lattices @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['263', '264'])).
% 0.47/0.66  thf('266', plain, ((v10_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('267', plain, ((l3_lattices @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('268', plain, ((v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('demod', [status(thm)], ['265', '266', '267'])).
% 0.47/0.66  thf('269', plain, ($false), inference('demod', [status(thm)], ['0', '268'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
