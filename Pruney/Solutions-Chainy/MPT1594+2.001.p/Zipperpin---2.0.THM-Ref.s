%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PtAPx1UrVC

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:03 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  214 (1326 expanded)
%              Number of leaves         :   49 ( 466 expanded)
%              Depth                    :   24
%              Number of atoms          : 1864 (13788 expanded)
%              Number of equality atoms :   55 ( 588 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_lattice3_type,type,(
    k4_lattice3: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k2_lattice3_type,type,(
    k2_lattice3: $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(t2_yellow_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
         => ( ( r3_orders_2 @ ( k3_yellow_1 @ A ) @ B @ C )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
           => ( ( r3_orders_2 @ ( k3_yellow_1 @ A ) @ B @ C )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_yellow_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
   <= ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('6',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf(d2_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ( k3_lattice3 @ A )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k2_lattice3 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( ( ( k3_lattice3 @ X11 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X11 ) @ ( k2_lattice3 @ X11 ) ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_lattice3])).

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

thf('8',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( k2_lattice3 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v10_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattice3])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_orders_2 @ X5 @ X6 )
       != ( g1_orders_2 @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k2_lattice3 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k3_lattice3 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_yellow_1 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) )
      | ( ( u1_struct_0 @ ( k1_lattice3 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf(fc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( v10_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('14',plain,(
    ! [X20: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf(dt_k1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_yellow_1 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ( ( u1_struct_0 @ ( k1_lattice3 @ X0 ) )
        = X2 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(fc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( v3_lattices @ ( k1_lattice3 @ A ) )
      & ~ ( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) )).

thf('17',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( k1_lattice3 @ X0 ) )
        = X2 )
      | ( ( k3_yellow_1 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_yellow_1 @ X1 )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X1: $i] :
      ( ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
        = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) )
      | ~ ( v1_orders_2 @ ( k3_yellow_1 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X11: $i] :
      ( ( ( k3_lattice3 @ X11 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X11 ) @ ( k2_lattice3 @ X11 ) ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_lattice3])).

thf('23',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( k2_lattice3 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v10_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattice3])).

thf(dt_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ( ( v1_orders_2 @ ( g1_orders_2 @ A @ B ) )
        & ( l1_orders_2 @ ( g1_orders_2 @ A @ B ) ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ( l1_orders_2 @ ( g1_orders_2 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( l1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k2_lattice3 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( l1_orders_2 @ ( k3_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X20: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('30',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('33',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('35',plain,(
    ! [X11: $i] :
      ( ( ( k3_lattice3 @ X11 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X11 ) @ ( k2_lattice3 @ X11 ) ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_lattice3])).

thf('36',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( k2_lattice3 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v10_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattice3])).

thf('37',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_orders_2 @ ( g1_orders_2 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k2_lattice3 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_orders_2 @ ( k3_lattice3 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_orders_2 @ ( k3_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X20: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('43',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('46',plain,(
    ! [X0: $i] :
      ( v1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf(d3_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattice3 @ A @ B )
            = B ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattice3 @ X13 @ X12 )
        = X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) )
      | ( ( k4_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X20: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('51',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ( ( k4_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['4','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('58',plain,
    ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t7_lattice3,axiom,(
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

thf('59',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ X25 ) @ ( k4_lattice3 @ X25 @ X24 ) @ ( k4_lattice3 @ X25 @ X26 ) )
      | ( r3_lattices @ X25 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_lattice3])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ ( k1_lattice3 @ sk_A ) ) @ sk_B @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    ! [X20: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('63',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('64',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf('65',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65','66'])).

thf('68',plain,
    ( ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('72',plain,
    ( ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf(redefinition_r3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_lattices @ A @ B @ C )
      <=> ( r1_lattices @ A @ B @ C ) ) ) )).

thf('77',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v9_lattices @ X9 )
      | ~ ( v8_lattices @ X9 )
      | ~ ( v6_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( r1_lattices @ X9 @ X8 @ X10 )
      | ~ ( r3_lattices @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( r3_lattices @ ( k1_lattice3 @ X0 ) @ X1 @ X2 )
      | ( r1_lattices @ ( k1_lattice3 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_lattice3 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v6_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v8_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v9_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf(cc1_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v4_lattices @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A ) ) ) ) )).

thf('80',plain,(
    ! [X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v6_lattices @ X7 )
      | ~ ( l3_lattices @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('81',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) )
      | ( v6_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('84',plain,(
    ! [X20: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('85',plain,(
    ! [X0: $i] :
      ( v6_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v8_lattices @ X7 )
      | ~ ( l3_lattices @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('87',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) )
      | ( v8_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('90',plain,(
    ! [X20: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('91',plain,(
    ! [X0: $i] :
      ( v8_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v9_lattices @ X7 )
      | ~ ( l3_lattices @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('93',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) )
      | ( v9_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('96',plain,(
    ! [X20: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('97',plain,(
    ! [X0: $i] :
      ( v9_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( r3_lattices @ ( k1_lattice3 @ X0 ) @ X1 @ X2 )
      | ( r1_lattices @ ( k1_lattice3 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['78','79','85','91','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','99'])).

thf('101',plain,
    ( ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','100'])).

thf('102',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('103',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['73','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) )
         => ( ( r1_lattices @ ( k1_lattice3 @ A ) @ B @ C )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf('107',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k1_lattice3 @ X22 ) ) )
      | ~ ( r1_lattices @ ( k1_lattice3 @ X22 ) @ X23 @ X21 )
      | ( r1_tarski @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k1_lattice3 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t2_lattice3])).

thf('108',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf('109',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf('110',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) )
      | ~ ( r1_lattices @ ( k1_lattice3 @ X22 ) @ X23 @ X21 )
      | ( r1_tarski @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_C )
      | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','110'])).

thf('112',plain,
    ( ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['104','112'])).

thf('114',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('117',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k1_lattice3 @ X22 ) ) )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ( r1_lattices @ ( k1_lattice3 @ X22 ) @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k1_lattice3 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t2_lattice3])).

thf('121',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf('122',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf('123',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ( r1_lattices @ ( k1_lattice3 @ X22 ) @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ X0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','123'])).

thf('125',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['118','124'])).

thf('126',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf('130',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v9_lattices @ X9 )
      | ~ ( v8_lattices @ X9 )
      | ~ ( v6_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( r3_lattices @ X9 @ X8 @ X10 )
      | ~ ( r1_lattices @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( r1_lattices @ ( k1_lattice3 @ X0 ) @ X1 @ X2 )
      | ( r3_lattices @ ( k1_lattice3 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_lattice3 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v6_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v8_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v9_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf('133',plain,(
    ! [X0: $i] :
      ( v6_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('134',plain,(
    ! [X0: $i] :
      ( v8_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('135',plain,(
    ! [X0: $i] :
      ( v9_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('136',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( r1_lattices @ ( k1_lattice3 @ X0 ) @ X1 @ X2 )
      | ( r3_lattices @ ( k1_lattice3 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','137'])).

thf('139',plain,
    ( ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','138'])).

thf('140',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('141',plain,
    ( ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['126','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf('145',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r3_lattices @ X25 @ X24 @ X26 )
      | ( r3_orders_2 @ ( k3_lattice3 @ X25 ) @ ( k4_lattice3 @ X25 @ X24 ) @ ( k4_lattice3 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_lattice3])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_lattice3 @ X0 ) ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ ( k1_lattice3 @ X0 ) ) @ ( k4_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 ) @ ( k4_lattice3 @ ( k1_lattice3 @ X0 ) @ X2 ) )
      | ~ ( r3_lattices @ ( k1_lattice3 @ X0 ) @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X20: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('148',plain,(
    ! [X15: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('149',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k1_lattice3 @ X1 ) )
      = ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','33','46'])).

thf('150',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( r3_orders_2 @ ( k3_yellow_1 @ X0 ) @ ( k4_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 ) @ ( k4_lattice3 @ ( k1_lattice3 @ X0 ) @ X2 ) )
      | ~ ( r3_lattices @ ( k1_lattice3 @ X0 ) @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_B ) @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['143','151'])).

thf('153',plain,
    ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_C ) ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['142','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['4','54'])).

thf('158',plain,
    ( ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,(
    ! [X17: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('160',plain,
    ( ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
   <= ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('162',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','115','116','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PtAPx1UrVC
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 210 iterations in 0.099s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.37/0.55  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.37/0.55  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.37/0.55  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.37/0.55  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.37/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.55  thf(k4_lattice3_type, type, k4_lattice3: $i > $i > $i).
% 0.37/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.37/0.55  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.37/0.55  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.37/0.55  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.37/0.55  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.37/0.55  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.37/0.55  thf(k2_lattice3_type, type, k2_lattice3: $i > $i).
% 0.37/0.55  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.37/0.55  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.37/0.55  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.37/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.37/0.55  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.37/0.55  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.37/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.55  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.37/0.55  thf(t2_yellow_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.37/0.55           ( ( r3_orders_2 @ ( k3_yellow_1 @ A ) @ B @ C ) <=>
% 0.37/0.55             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.37/0.55          ( ![C:$i]:
% 0.37/0.55            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.37/0.55              ( ( r3_orders_2 @ ( k3_yellow_1 @ A ) @ B @ C ) <=>
% 0.37/0.55                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t2_yellow_1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.37/0.55        | ~ (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.37/0.55       ~ ((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (((r1_tarski @ sk_B @ sk_C)
% 0.37/0.55        | (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.37/0.55         <= (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.37/0.55      inference('split', [status(esa)], ['2'])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(abstractness_v1_orders_2, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_orders_2 @ A ) =>
% 0.37/0.55       ( ( v1_orders_2 @ A ) =>
% 0.37/0.55         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_orders_2 @ X0)
% 0.37/0.55          | ((X0) = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.37/0.55          | ~ (l1_orders_2 @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.37/0.55  thf(d2_yellow_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf(d2_lattice3, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.37/0.55       ( ( k3_lattice3 @ A ) =
% 0.37/0.55         ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k2_lattice3 @ A ) ) ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X11 : $i]:
% 0.37/0.55         (((k3_lattice3 @ X11)
% 0.37/0.55            = (g1_orders_2 @ (u1_struct_0 @ X11) @ (k2_lattice3 @ X11)))
% 0.37/0.55          | ~ (l3_lattices @ X11)
% 0.37/0.55          | ~ (v10_lattices @ X11)
% 0.37/0.55          | (v2_struct_0 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_lattice3])).
% 0.37/0.55  thf(dt_k2_lattice3, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.37/0.55       ( ( v1_partfun1 @ ( k2_lattice3 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.37/0.55         ( v1_relat_2 @ ( k2_lattice3 @ A ) ) & 
% 0.37/0.55         ( v4_relat_2 @ ( k2_lattice3 @ A ) ) & 
% 0.37/0.55         ( v8_relat_2 @ ( k2_lattice3 @ A ) ) & 
% 0.37/0.55         ( m1_subset_1 @
% 0.37/0.55           ( k2_lattice3 @ A ) @ 
% 0.37/0.55           ( k1_zfmisc_1 @
% 0.37/0.55             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X16 : $i]:
% 0.37/0.55         ((m1_subset_1 @ (k2_lattice3 @ X16) @ 
% 0.37/0.55           (k1_zfmisc_1 @ 
% 0.37/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X16))))
% 0.37/0.55          | ~ (l3_lattices @ X16)
% 0.37/0.55          | ~ (v10_lattices @ X16)
% 0.37/0.55          | (v2_struct_0 @ X16))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k2_lattice3])).
% 0.37/0.55  thf(free_g1_orders_2, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.37/0.55       ( ![C:$i,D:$i]:
% 0.37/0.55         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.37/0.55           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.55         (((g1_orders_2 @ X5 @ X6) != (g1_orders_2 @ X3 @ X4))
% 0.37/0.55          | ((X5) = (X3))
% 0.37/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5))))),
% 0.37/0.55      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | ~ (l3_lattices @ X0)
% 0.37/0.55          | ((u1_struct_0 @ X0) = (X1))
% 0.37/0.55          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (k2_lattice3 @ X0))
% 0.37/0.55              != (g1_orders_2 @ X1 @ X2)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (((k3_lattice3 @ X0) != (g1_orders_2 @ X2 @ X1))
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | ~ (l3_lattices @ X0)
% 0.37/0.55          | ((u1_struct_0 @ X0) = (X2))
% 0.37/0.55          | ~ (l3_lattices @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | (v2_struct_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '10'])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (((u1_struct_0 @ X0) = (X2))
% 0.37/0.55          | ~ (l3_lattices @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ((k3_lattice3 @ X0) != (g1_orders_2 @ X2 @ X1)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (((k3_yellow_1 @ X0) != (g1_orders_2 @ X2 @ X1))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (l3_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ((u1_struct_0 @ (k1_lattice3 @ X0)) = (X2)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '12'])).
% 0.37/0.55  thf(fc2_lattice3, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v10_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.37/0.55       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.37/0.55  thf('14', plain, (![X20 : $i]: (v10_lattices @ (k1_lattice3 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.37/0.55  thf(dt_k1_lattice3, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.37/0.55       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.37/0.55  thf('15', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (((k3_yellow_1 @ X0) != (g1_orders_2 @ X2 @ X1))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.37/0.55          | ((u1_struct_0 @ (k1_lattice3 @ X0)) = (X2)))),
% 0.37/0.55      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.37/0.55  thf(fc1_lattice3, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.37/0.55       ( ~( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) ))).
% 0.37/0.55  thf('17', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (((u1_struct_0 @ (k1_lattice3 @ X0)) = (X2))
% 0.37/0.55          | ((k3_yellow_1 @ X0) != (g1_orders_2 @ X2 @ X1)))),
% 0.37/0.55      inference('clc', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k3_yellow_1 @ X1) != (X0))
% 0.37/0.55          | ~ (l1_orders_2 @ X0)
% 0.37/0.55          | ~ (v1_orders_2 @ X0)
% 0.37/0.55          | ((u1_struct_0 @ (k1_lattice3 @ X1)) = (u1_struct_0 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['5', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         (((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55            = (u1_struct_0 @ (k3_yellow_1 @ X1)))
% 0.37/0.55          | ~ (v1_orders_2 @ (k3_yellow_1 @ X1))
% 0.37/0.55          | ~ (l1_orders_2 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X11 : $i]:
% 0.37/0.55         (((k3_lattice3 @ X11)
% 0.37/0.55            = (g1_orders_2 @ (u1_struct_0 @ X11) @ (k2_lattice3 @ X11)))
% 0.37/0.55          | ~ (l3_lattices @ X11)
% 0.37/0.55          | ~ (v10_lattices @ X11)
% 0.37/0.55          | (v2_struct_0 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_lattice3])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X16 : $i]:
% 0.37/0.55         ((m1_subset_1 @ (k2_lattice3 @ X16) @ 
% 0.37/0.55           (k1_zfmisc_1 @ 
% 0.37/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X16))))
% 0.37/0.55          | ~ (l3_lattices @ X16)
% 0.37/0.55          | ~ (v10_lattices @ X16)
% 0.37/0.55          | (v2_struct_0 @ X16))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k2_lattice3])).
% 0.37/0.55  thf(dt_g1_orders_2, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.37/0.55       ( ( v1_orders_2 @ ( g1_orders_2 @ A @ B ) ) & 
% 0.37/0.55         ( l1_orders_2 @ ( g1_orders_2 @ A @ B ) ) ) ))).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i]:
% 0.37/0.55         ((l1_orders_2 @ (g1_orders_2 @ X1 @ X2))
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X1))))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_g1_orders_2])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | ~ (l3_lattices @ X0)
% 0.37/0.55          | (l1_orders_2 @ 
% 0.37/0.55             (g1_orders_2 @ (u1_struct_0 @ X0) @ (k2_lattice3 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((l1_orders_2 @ (k3_lattice3 @ X0))
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | ~ (l3_lattices @ X0)
% 0.37/0.55          | ~ (l3_lattices @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | (v2_struct_0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['22', '25'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l3_lattices @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | (l1_orders_2 @ (k3_lattice3 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((l1_orders_2 @ (k3_yellow_1 @ X0))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['21', '27'])).
% 0.37/0.55  thf('29', plain, (![X20 : $i]: (v10_lattices @ (k1_lattice3 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.37/0.55  thf('30', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((l1_orders_2 @ (k3_yellow_1 @ X0))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.37/0.55  thf('32', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('33', plain, (![X0 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X0))),
% 0.37/0.55      inference('clc', [status(thm)], ['31', '32'])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X11 : $i]:
% 0.37/0.55         (((k3_lattice3 @ X11)
% 0.37/0.55            = (g1_orders_2 @ (u1_struct_0 @ X11) @ (k2_lattice3 @ X11)))
% 0.37/0.55          | ~ (l3_lattices @ X11)
% 0.37/0.55          | ~ (v10_lattices @ X11)
% 0.37/0.55          | (v2_struct_0 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_lattice3])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X16 : $i]:
% 0.37/0.55         ((m1_subset_1 @ (k2_lattice3 @ X16) @ 
% 0.37/0.55           (k1_zfmisc_1 @ 
% 0.37/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X16))))
% 0.37/0.55          | ~ (l3_lattices @ X16)
% 0.37/0.55          | ~ (v10_lattices @ X16)
% 0.37/0.55          | (v2_struct_0 @ X16))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k2_lattice3])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i]:
% 0.37/0.55         ((v1_orders_2 @ (g1_orders_2 @ X1 @ X2))
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X1))))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_g1_orders_2])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | ~ (l3_lattices @ X0)
% 0.37/0.55          | (v1_orders_2 @ 
% 0.37/0.55             (g1_orders_2 @ (u1_struct_0 @ X0) @ (k2_lattice3 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v1_orders_2 @ (k3_lattice3 @ X0))
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | ~ (l3_lattices @ X0)
% 0.37/0.55          | ~ (l3_lattices @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | (v2_struct_0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['35', '38'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l3_lattices @ X0)
% 0.37/0.55          | ~ (v10_lattices @ X0)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | (v1_orders_2 @ (k3_lattice3 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v1_orders_2 @ (k3_yellow_1 @ X0))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['34', '40'])).
% 0.37/0.55  thf('42', plain, (![X20 : $i]: (v10_lattices @ (k1_lattice3 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.37/0.55  thf('43', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v1_orders_2 @ (k3_yellow_1 @ X0))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.37/0.55  thf('45', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('46', plain, (![X0 : $i]: (v1_orders_2 @ (k3_yellow_1 @ X0))),
% 0.37/0.55      inference('clc', [status(thm)], ['44', '45'])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf(d3_lattice3, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.55           ( ( k4_lattice3 @ A @ B ) = ( B ) ) ) ) ))).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.37/0.55          | ((k4_lattice3 @ X13 @ X12) = (X12))
% 0.37/0.55          | ~ (l3_lattices @ X13)
% 0.37/0.55          | ~ (v10_lattices @ X13)
% 0.37/0.55          | (v2_struct_0 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_lattice3])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (l3_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ((k4_lattice3 @ (k1_lattice3 @ X0) @ X1) = (X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.55  thf('50', plain, (![X20 : $i]: (v10_lattices @ (k1_lattice3 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.37/0.55  thf('51', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.37/0.55          | ((k4_lattice3 @ (k1_lattice3 @ X0) @ X1) = (X1)))),
% 0.37/0.55      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.37/0.55  thf('53', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('54', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k4_lattice3 @ (k1_lattice3 @ X0) @ X1) = (X1))
% 0.37/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0))))),
% 0.37/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.37/0.55  thf('55', plain, (((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_C) = (sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '54'])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k4_lattice3 @ (k1_lattice3 @ X0) @ X1) = (X1))
% 0.37/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0))))),
% 0.37/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.37/0.55  thf('58', plain, (((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_B) = (sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf(t7_lattice3, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.55               ( ( r3_lattices @ A @ B @ C ) <=>
% 0.37/0.55                 ( r3_orders_2 @
% 0.37/0.55                   ( k3_lattice3 @ A ) @ ( k4_lattice3 @ A @ B ) @ 
% 0.37/0.55                   ( k4_lattice3 @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf('59', plain,
% 0.37/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.37/0.55          | ~ (r3_orders_2 @ (k3_lattice3 @ X25) @ (k4_lattice3 @ X25 @ X24) @ 
% 0.37/0.55               (k4_lattice3 @ X25 @ X26))
% 0.37/0.55          | (r3_lattices @ X25 @ X24 @ X26)
% 0.37/0.55          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.37/0.55          | ~ (l3_lattices @ X25)
% 0.37/0.55          | ~ (v10_lattices @ X25)
% 0.37/0.55          | (v2_struct_0 @ X25))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_lattice3])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r3_orders_2 @ (k3_lattice3 @ (k1_lattice3 @ sk_A)) @ sk_B @ 
% 0.37/0.55             (k4_lattice3 @ (k1_lattice3 @ sk_A) @ X0))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.37/0.55          | ~ (v10_lattices @ (k1_lattice3 @ sk_A))
% 0.37/0.55          | ~ (l3_lattices @ (k1_lattice3 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.37/0.55          | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.37/0.55          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('62', plain, (![X20 : $i]: (v10_lattices @ (k1_lattice3 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.37/0.55  thf('63', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ 
% 0.37/0.55             (k4_lattice3 @ (k1_lattice3 @ sk_A) @ X0))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.37/0.55          | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0))),
% 0.37/0.55      inference('demod', [status(thm)],
% 0.37/0.55                ['60', '61', '62', '63', '64', '65', '66'])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      ((~ (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.37/0.55        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['55', '67'])).
% 0.37/0.55  thf('69', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('70', plain,
% 0.37/0.55      ((~ (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['68', '69'])).
% 0.37/0.55  thf('71', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('72', plain,
% 0.37/0.55      (((r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | ~ (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.37/0.55      inference('clc', [status(thm)], ['70', '71'])).
% 0.37/0.55  thf('73', plain,
% 0.37/0.55      (((r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.37/0.55         <= (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '72'])).
% 0.37/0.55  thf('74', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('75', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('76', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf(redefinition_r3_lattices, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.37/0.55         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.37/0.55         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.37/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.37/0.55  thf('77', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.37/0.55          | ~ (l3_lattices @ X9)
% 0.37/0.55          | ~ (v9_lattices @ X9)
% 0.37/0.55          | ~ (v8_lattices @ X9)
% 0.37/0.55          | ~ (v6_lattices @ X9)
% 0.37/0.55          | (v2_struct_0 @ X9)
% 0.37/0.55          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.37/0.55          | (r1_lattices @ X9 @ X8 @ X10)
% 0.37/0.55          | ~ (r3_lattices @ X9 @ X8 @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.37/0.55  thf('78', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | ~ (r3_lattices @ (k1_lattice3 @ X0) @ X1 @ X2)
% 0.37/0.55          | (r1_lattices @ (k1_lattice3 @ X0) @ X1 @ X2)
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_lattice3 @ X0)))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v6_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v8_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v9_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['76', '77'])).
% 0.37/0.55  thf('79', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf(cc1_lattices, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l3_lattices @ A ) =>
% 0.37/0.55       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.37/0.55         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.37/0.55           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.37/0.55           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.37/0.55  thf('80', plain,
% 0.37/0.55      (![X7 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X7)
% 0.37/0.55          | ~ (v10_lattices @ X7)
% 0.37/0.55          | (v6_lattices @ X7)
% 0.37/0.55          | ~ (l3_lattices @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.37/0.55  thf('81', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('82', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l3_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | (v6_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v10_lattices @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['80', '81'])).
% 0.37/0.55  thf('83', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('84', plain, (![X20 : $i]: (v10_lattices @ (k1_lattice3 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.37/0.55  thf('85', plain, (![X0 : $i]: (v6_lattices @ (k1_lattice3 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.37/0.55  thf('86', plain,
% 0.37/0.55      (![X7 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X7)
% 0.37/0.55          | ~ (v10_lattices @ X7)
% 0.37/0.55          | (v8_lattices @ X7)
% 0.37/0.55          | ~ (l3_lattices @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.37/0.55  thf('87', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('88', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l3_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | (v8_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v10_lattices @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['86', '87'])).
% 0.37/0.55  thf('89', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('90', plain, (![X20 : $i]: (v10_lattices @ (k1_lattice3 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.37/0.55  thf('91', plain, (![X0 : $i]: (v8_lattices @ (k1_lattice3 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.37/0.55  thf('92', plain,
% 0.37/0.55      (![X7 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X7)
% 0.37/0.55          | ~ (v10_lattices @ X7)
% 0.37/0.55          | (v9_lattices @ X7)
% 0.37/0.55          | ~ (l3_lattices @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.37/0.55  thf('93', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('94', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l3_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | (v9_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v10_lattices @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['92', '93'])).
% 0.37/0.55  thf('95', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('96', plain, (![X20 : $i]: (v10_lattices @ (k1_lattice3 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.37/0.55  thf('97', plain, (![X0 : $i]: (v9_lattices @ (k1_lattice3 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.37/0.55  thf('98', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('99', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | ~ (r3_lattices @ (k1_lattice3 @ X0) @ X1 @ X2)
% 0.37/0.55          | (r1_lattices @ (k1_lattice3 @ X0) @ X1 @ X2)
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['78', '79', '85', '91', '97', '98'])).
% 0.37/0.55  thf('100', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.37/0.55          | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.37/0.55          | ~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['75', '99'])).
% 0.37/0.55  thf('101', plain,
% 0.37/0.55      ((~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['74', '100'])).
% 0.37/0.55  thf('102', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('103', plain,
% 0.37/0.55      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | ~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.37/0.55      inference('clc', [status(thm)], ['101', '102'])).
% 0.37/0.55  thf('104', plain,
% 0.37/0.55      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.37/0.55         <= (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['73', '103'])).
% 0.37/0.55  thf('105', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('106', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t2_lattice3, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.37/0.55           ( ( r1_lattices @ ( k1_lattice3 @ A ) @ B @ C ) <=>
% 0.37/0.55             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.37/0.55  thf('107', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k1_lattice3 @ X22)))
% 0.37/0.55          | ~ (r1_lattices @ (k1_lattice3 @ X22) @ X23 @ X21)
% 0.37/0.55          | (r1_tarski @ X23 @ X21)
% 0.37/0.55          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k1_lattice3 @ X22))))),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_lattice3])).
% 0.37/0.55  thf('108', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf('109', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf('110', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k3_yellow_1 @ X22)))
% 0.37/0.55          | ~ (r1_lattices @ (k1_lattice3 @ X22) @ X23 @ X21)
% 0.37/0.55          | (r1_tarski @ X23 @ X21)
% 0.37/0.55          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k3_yellow_1 @ X22))))),
% 0.37/0.55      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.37/0.55  thf('111', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.37/0.55          | (r1_tarski @ X0 @ sk_C)
% 0.37/0.55          | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ X0 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['106', '110'])).
% 0.37/0.55  thf('112', plain,
% 0.37/0.55      ((~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | (r1_tarski @ sk_B @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['105', '111'])).
% 0.37/0.55  thf('113', plain,
% 0.37/0.55      (((r1_tarski @ sk_B @ sk_C))
% 0.37/0.55         <= (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['104', '112'])).
% 0.37/0.55  thf('114', plain,
% 0.37/0.55      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('115', plain,
% 0.37/0.55      (((r1_tarski @ sk_B @ sk_C)) | 
% 0.37/0.55       ~ ((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['113', '114'])).
% 0.37/0.55  thf('116', plain,
% 0.37/0.55      (((r1_tarski @ sk_B @ sk_C)) | 
% 0.37/0.55       ((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.37/0.55      inference('split', [status(esa)], ['2'])).
% 0.37/0.55  thf('117', plain,
% 0.37/0.55      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.37/0.55      inference('split', [status(esa)], ['2'])).
% 0.37/0.55  thf('118', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('119', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('120', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k1_lattice3 @ X22)))
% 0.37/0.55          | ~ (r1_tarski @ X23 @ X21)
% 0.37/0.55          | (r1_lattices @ (k1_lattice3 @ X22) @ X23 @ X21)
% 0.37/0.55          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k1_lattice3 @ X22))))),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_lattice3])).
% 0.37/0.55  thf('121', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf('122', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf('123', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k3_yellow_1 @ X22)))
% 0.37/0.55          | ~ (r1_tarski @ X23 @ X21)
% 0.37/0.55          | (r1_lattices @ (k1_lattice3 @ X22) @ X23 @ X21)
% 0.37/0.55          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k3_yellow_1 @ X22))))),
% 0.37/0.55      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.37/0.55  thf('124', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.37/0.55          | (r1_lattices @ (k1_lattice3 @ sk_A) @ X0 @ sk_C)
% 0.37/0.55          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['119', '123'])).
% 0.37/0.55  thf('125', plain,
% 0.37/0.55      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.37/0.55        | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['118', '124'])).
% 0.37/0.55  thf('126', plain,
% 0.37/0.55      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.37/0.55         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['117', '125'])).
% 0.37/0.55  thf('127', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('128', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('129', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf('130', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.37/0.55          | ~ (l3_lattices @ X9)
% 0.37/0.55          | ~ (v9_lattices @ X9)
% 0.37/0.55          | ~ (v8_lattices @ X9)
% 0.37/0.55          | ~ (v6_lattices @ X9)
% 0.37/0.55          | (v2_struct_0 @ X9)
% 0.37/0.55          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.37/0.55          | (r3_lattices @ X9 @ X8 @ X10)
% 0.37/0.55          | ~ (r1_lattices @ X9 @ X8 @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.37/0.55  thf('131', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | ~ (r1_lattices @ (k1_lattice3 @ X0) @ X1 @ X2)
% 0.37/0.55          | (r3_lattices @ (k1_lattice3 @ X0) @ X1 @ X2)
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_lattice3 @ X0)))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v6_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v8_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v9_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['129', '130'])).
% 0.37/0.55  thf('132', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf('133', plain, (![X0 : $i]: (v6_lattices @ (k1_lattice3 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.37/0.55  thf('134', plain, (![X0 : $i]: (v8_lattices @ (k1_lattice3 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.37/0.55  thf('135', plain, (![X0 : $i]: (v9_lattices @ (k1_lattice3 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.37/0.55  thf('136', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('137', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | ~ (r1_lattices @ (k1_lattice3 @ X0) @ X1 @ X2)
% 0.37/0.55          | (r3_lattices @ (k1_lattice3 @ X0) @ X1 @ X2)
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)],
% 0.37/0.55                ['131', '132', '133', '134', '135', '136'])).
% 0.37/0.55  thf('138', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.37/0.55          | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.37/0.55          | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['128', '137'])).
% 0.37/0.55  thf('139', plain,
% 0.37/0.55      ((~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['127', '138'])).
% 0.37/0.55  thf('140', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('141', plain,
% 0.37/0.55      (((r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.37/0.55        | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.37/0.55      inference('clc', [status(thm)], ['139', '140'])).
% 0.37/0.55  thf('142', plain,
% 0.37/0.55      (((r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.37/0.55         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['126', '141'])).
% 0.37/0.55  thf('143', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('144', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf('145', plain,
% 0.37/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.37/0.55          | ~ (r3_lattices @ X25 @ X24 @ X26)
% 0.37/0.55          | (r3_orders_2 @ (k3_lattice3 @ X25) @ (k4_lattice3 @ X25 @ X24) @ 
% 0.37/0.55             (k4_lattice3 @ X25 @ X26))
% 0.37/0.55          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.37/0.55          | ~ (l3_lattices @ X25)
% 0.37/0.55          | ~ (v10_lattices @ X25)
% 0.37/0.55          | (v2_struct_0 @ X25))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_lattice3])).
% 0.37/0.55  thf('146', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (l3_lattices @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_lattice3 @ X0)))
% 0.37/0.55          | (r3_orders_2 @ (k3_lattice3 @ (k1_lattice3 @ X0)) @ 
% 0.37/0.55             (k4_lattice3 @ (k1_lattice3 @ X0) @ X1) @ 
% 0.37/0.55             (k4_lattice3 @ (k1_lattice3 @ X0) @ X2))
% 0.37/0.55          | ~ (r3_lattices @ (k1_lattice3 @ X0) @ X1 @ X2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['144', '145'])).
% 0.37/0.55  thf('147', plain, (![X20 : $i]: (v10_lattices @ (k1_lattice3 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.37/0.55  thf('148', plain, (![X15 : $i]: (l3_lattices @ (k1_lattice3 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.37/0.55  thf('149', plain,
% 0.37/0.55      (![X1 : $i]:
% 0.37/0.55         ((u1_struct_0 @ (k1_lattice3 @ X1))
% 0.37/0.55           = (u1_struct_0 @ (k3_yellow_1 @ X1)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['20', '33', '46'])).
% 0.37/0.55  thf('150', plain,
% 0.37/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('151', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.37/0.55          | (r3_orders_2 @ (k3_yellow_1 @ X0) @ 
% 0.37/0.55             (k4_lattice3 @ (k1_lattice3 @ X0) @ X1) @ 
% 0.37/0.55             (k4_lattice3 @ (k1_lattice3 @ X0) @ X2))
% 0.37/0.55          | ~ (r3_lattices @ (k1_lattice3 @ X0) @ X1 @ X2))),
% 0.37/0.55      inference('demod', [status(thm)], ['146', '147', '148', '149', '150'])).
% 0.37/0.55  thf('152', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.37/0.55          | (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ 
% 0.37/0.55             (k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_B) @ 
% 0.37/0.55             (k4_lattice3 @ (k1_lattice3 @ sk_A) @ X0))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['143', '151'])).
% 0.37/0.55  thf('153', plain, (((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_B) = (sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('154', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.37/0.55          | (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ 
% 0.37/0.55             (k4_lattice3 @ (k1_lattice3 @ sk_A) @ X0))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.37/0.55          | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['152', '153'])).
% 0.37/0.55  thf('155', plain,
% 0.37/0.55      ((((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.37/0.55         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.37/0.55         | (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ 
% 0.37/0.55            (k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_C))))
% 0.37/0.55         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['142', '154'])).
% 0.37/0.55  thf('156', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('157', plain, (((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_C) = (sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '54'])).
% 0.37/0.55  thf('158', plain,
% 0.37/0.55      ((((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.37/0.55         | (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 0.37/0.55         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.37/0.55      inference('demod', [status(thm)], ['155', '156', '157'])).
% 0.37/0.55  thf('159', plain, (![X17 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.37/0.55  thf('160', plain,
% 0.37/0.55      (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.37/0.55         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.37/0.55      inference('clc', [status(thm)], ['158', '159'])).
% 0.37/0.55  thf('161', plain,
% 0.37/0.55      ((~ (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.37/0.55         <= (~ ((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('162', plain,
% 0.37/0.55      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.37/0.55       ((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['160', '161'])).
% 0.37/0.55  thf('163', plain, ($false),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['1', '115', '116', '162'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
