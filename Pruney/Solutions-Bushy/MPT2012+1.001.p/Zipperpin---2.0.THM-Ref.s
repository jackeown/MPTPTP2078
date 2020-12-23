%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2012+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J6VufcSNyz

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  68 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  476 ( 683 expanded)
%              Number of equality atoms :   34 (  46 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_struct_0_type,type,(
    k3_struct_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k3_waybel_9_type,type,(
    k3_waybel_9: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(dt_k3_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v6_waybel_0 @ ( k3_waybel_9 @ A ) @ A )
        & ( l1_waybel_0 @ ( k3_waybel_9 @ A ) @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( l1_waybel_0 @ ( k3_waybel_9 @ X4 ) @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_9])).

thf(d6_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ( v6_waybel_0 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ( ( B
              = ( k3_waybel_9 @ A ) )
          <=> ( ( ( u1_struct_0 @ B )
                = ( u1_struct_0 @ A ) )
              & ( ( u1_orders_2 @ B )
                = ( k3_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) )
              & ( ( u1_waybel_0 @ A @ B )
                = ( k3_struct_0 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v6_waybel_0 @ X2 @ X3 )
      | ~ ( l1_waybel_0 @ X2 @ X3 )
      | ( X2
       != ( k3_waybel_9 @ X3 ) )
      | ( ( u1_orders_2 @ X2 )
        = ( k3_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) @ ( u1_orders_2 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_9])).

thf('2',plain,(
    ! [X3: $i] :
      ( ~ ( l1_orders_2 @ X3 )
      | ( ( u1_orders_2 @ ( k3_waybel_9 @ X3 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) @ ( u1_orders_2 @ X3 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_waybel_9 @ X3 ) @ X3 )
      | ~ ( v6_waybel_0 @ ( k3_waybel_9 @ X3 ) @ X3 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v6_waybel_0 @ ( k3_waybel_9 @ X0 ) @ X0 )
      | ( ( u1_orders_2 @ ( k3_waybel_9 @ X0 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( k3_waybel_9 @ X0 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( v6_waybel_0 @ ( k3_waybel_9 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( v6_waybel_0 @ ( k3_waybel_9 @ X4 ) @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_9])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k3_waybel_9 @ X0 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(d5_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k7_lattice3 @ A )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k3_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( ( k7_lattice3 @ X1 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k3_waybel_9 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k3_waybel_9 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X4: $i] :
      ( ( l1_waybel_0 @ ( k3_waybel_9 @ X4 ) @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_9])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v6_waybel_0 @ X2 @ X3 )
      | ~ ( l1_waybel_0 @ X2 @ X3 )
      | ( X2
       != ( k3_waybel_9 @ X3 ) )
      | ( ( u1_struct_0 @ X2 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_9])).

thf('12',plain,(
    ! [X3: $i] :
      ( ~ ( l1_orders_2 @ X3 )
      | ( ( u1_struct_0 @ ( k3_waybel_9 @ X3 ) )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_waybel_0 @ ( k3_waybel_9 @ X3 ) @ X3 )
      | ~ ( v6_waybel_0 @ ( k3_waybel_9 @ X3 ) @ X3 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v6_waybel_0 @ ( k3_waybel_9 @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ ( k3_waybel_9 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k3_waybel_9 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v6_waybel_0 @ ( k3_waybel_9 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( v6_waybel_0 @ ( k3_waybel_9 @ X4 ) @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_9])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k3_waybel_9 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(dt_k7_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( l1_orders_2 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(t11_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( g1_orders_2 @ ( u1_struct_0 @ ( k7_lattice3 @ A ) ) @ ( u1_orders_2 @ ( k7_lattice3 @ A ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_9 @ A ) ) @ ( u1_orders_2 @ ( k3_waybel_9 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ( ( g1_orders_2 @ ( u1_struct_0 @ ( k7_lattice3 @ A ) ) @ ( u1_orders_2 @ ( k7_lattice3 @ A ) ) )
          = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_9 @ A ) ) @ ( u1_orders_2 @ ( k3_waybel_9 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_waybel_9])).

thf('20',plain,(
    ( g1_orders_2 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
 != ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_9 @ sk_A ) ) @ ( u1_orders_2 @ ( k3_waybel_9 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k7_lattice3 @ sk_A )
     != ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_9 @ sk_A ) ) @ ( u1_orders_2 @ ( k3_waybel_9 @ sk_A ) ) ) )
    | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v1_orders_2 @ ( k7_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_orders_2 @ ( k7_lattice3 @ sk_A ) )
    | ( ( k7_lattice3 @ sk_A )
     != ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_9 @ sk_A ) ) @ ( u1_orders_2 @ ( k3_waybel_9 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_orders_2 @ ( k7_lattice3 @ sk_A ) )
    | ( ( k7_lattice3 @ sk_A )
     != ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_9 @ sk_A ) ) @ ( u1_orders_2 @ ( k3_waybel_9 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k7_lattice3 @ sk_A )
     != ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_9 @ sk_A ) ) @ ( u1_orders_2 @ ( k3_waybel_9 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ( k7_lattice3 @ sk_A )
 != ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_9 @ sk_A ) ) @ ( u1_orders_2 @ ( k3_waybel_9 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k7_lattice3 @ sk_A )
     != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ ( k3_waybel_9 @ sk_A ) ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k7_lattice3 @ sk_A )
 != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ ( k3_waybel_9 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k7_lattice3 @ sk_A )
     != ( k7_lattice3 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k7_lattice3 @ sk_A )
 != ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).


%------------------------------------------------------------------------------
