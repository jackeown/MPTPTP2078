%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t08NGEb7p3

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  68 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  476 ( 683 expanded)
%              Number of equality atoms :   34 (  46 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k3_struct_0_type,type,(
    k3_struct_0: $i > $i )).

thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k3_waybel_9_type,type,(
    k3_waybel_9: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(dt_k3_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v6_waybel_0 @ ( k3_waybel_9 @ A ) @ A )
        & ( l1_waybel_0 @ ( k3_waybel_9 @ A ) @ A ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( l1_waybel_0 @ ( k3_waybel_9 @ X5 ) @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v6_waybel_0 @ X3 @ X4 )
      | ~ ( l1_waybel_0 @ X3 @ X4 )
      | ( X3
       != ( k3_waybel_9 @ X4 ) )
      | ( ( u1_orders_2 @ X3 )
        = ( k3_relset_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) @ ( u1_orders_2 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_9])).

thf('2',plain,(
    ! [X4: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( ( u1_orders_2 @ ( k3_waybel_9 @ X4 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) @ ( u1_orders_2 @ X4 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_waybel_9 @ X4 ) @ X4 )
      | ~ ( v6_waybel_0 @ ( k3_waybel_9 @ X4 ) @ X4 ) ) ),
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
    ! [X5: $i] :
      ( ( v6_waybel_0 @ ( k3_waybel_9 @ X5 ) @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
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
    ! [X5: $i] :
      ( ( l1_waybel_0 @ ( k3_waybel_9 @ X5 ) @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_9])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v6_waybel_0 @ X3 @ X4 )
      | ~ ( l1_waybel_0 @ X3 @ X4 )
      | ( X3
       != ( k3_waybel_9 @ X4 ) )
      | ( ( u1_struct_0 @ X3 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_9])).

thf('12',plain,(
    ! [X4: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( ( u1_struct_0 @ ( k3_waybel_9 @ X4 ) )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_waybel_0 @ ( k3_waybel_9 @ X4 ) @ X4 )
      | ~ ( v6_waybel_0 @ ( k3_waybel_9 @ X4 ) @ X4 ) ) ),
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
    ! [X5: $i] :
      ( ( v6_waybel_0 @ ( k3_waybel_9 @ X5 ) @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
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
    ! [X2: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
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
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t08NGEb7p3
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:18:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 24 iterations in 0.021s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.48  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.22/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.48  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.22/0.48  thf(k3_struct_0_type, type, k3_struct_0: $i > $i).
% 0.22/0.48  thf(k7_lattice3_type, type, k7_lattice3: $i > $i).
% 0.22/0.48  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.22/0.48  thf(k3_waybel_9_type, type, k3_waybel_9: $i > $i).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.22/0.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.22/0.48  thf(dt_k3_waybel_9, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( ( v6_waybel_0 @ ( k3_waybel_9 @ A ) @ A ) & 
% 0.22/0.48         ( l1_waybel_0 @ ( k3_waybel_9 @ A ) @ A ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X5 : $i]:
% 0.22/0.48         ((l1_waybel_0 @ (k3_waybel_9 @ X5) @ X5) | ~ (l1_orders_2 @ X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k3_waybel_9])).
% 0.22/0.48  thf(d6_waybel_9, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( ( v6_waybel_0 @ B @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.48           ( ( ( B ) = ( k3_waybel_9 @ A ) ) <=>
% 0.22/0.48             ( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.48               ( ( u1_orders_2 @ B ) =
% 0.22/0.48                 ( k3_relset_1 @
% 0.22/0.48                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.48                   ( u1_orders_2 @ A ) ) ) & 
% 0.22/0.48               ( ( u1_waybel_0 @ A @ B ) = ( k3_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (v6_waybel_0 @ X3 @ X4)
% 0.22/0.48          | ~ (l1_waybel_0 @ X3 @ X4)
% 0.22/0.48          | ((X3) != (k3_waybel_9 @ X4))
% 0.22/0.48          | ((u1_orders_2 @ X3)
% 0.22/0.48              = (k3_relset_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X4) @ 
% 0.22/0.48                 (u1_orders_2 @ X4)))
% 0.22/0.48          | ~ (l1_orders_2 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [d6_waybel_9])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X4 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X4)
% 0.22/0.48          | ((u1_orders_2 @ (k3_waybel_9 @ X4))
% 0.22/0.48              = (k3_relset_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X4) @ 
% 0.22/0.48                 (u1_orders_2 @ X4)))
% 0.22/0.48          | ~ (l1_waybel_0 @ (k3_waybel_9 @ X4) @ X4)
% 0.22/0.48          | ~ (v6_waybel_0 @ (k3_waybel_9 @ X4) @ X4))),
% 0.22/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X0)
% 0.22/0.48          | ~ (v6_waybel_0 @ (k3_waybel_9 @ X0) @ X0)
% 0.22/0.48          | ((u1_orders_2 @ (k3_waybel_9 @ X0))
% 0.22/0.48              = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.22/0.48                 (u1_orders_2 @ X0)))
% 0.22/0.48          | ~ (l1_orders_2 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '2'])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((u1_orders_2 @ (k3_waybel_9 @ X0))
% 0.22/0.48            = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.22/0.48               (u1_orders_2 @ X0)))
% 0.22/0.48          | ~ (v6_waybel_0 @ (k3_waybel_9 @ X0) @ X0)
% 0.22/0.48          | ~ (l1_orders_2 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X5 : $i]:
% 0.22/0.48         ((v6_waybel_0 @ (k3_waybel_9 @ X5) @ X5) | ~ (l1_orders_2 @ X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k3_waybel_9])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X0)
% 0.22/0.48          | ((u1_orders_2 @ (k3_waybel_9 @ X0))
% 0.22/0.48              = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.22/0.48                 (u1_orders_2 @ X0))))),
% 0.22/0.48      inference('clc', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(d5_lattice3, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( ( k7_lattice3 @ A ) =
% 0.22/0.48         ( g1_orders_2 @
% 0.22/0.48           ( u1_struct_0 @ A ) @ 
% 0.22/0.48           ( k3_relset_1 @
% 0.22/0.48             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X1 : $i]:
% 0.22/0.48         (((k7_lattice3 @ X1)
% 0.22/0.48            = (g1_orders_2 @ (u1_struct_0 @ X1) @ 
% 0.22/0.48               (k3_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X1) @ 
% 0.22/0.48                (u1_orders_2 @ X1))))
% 0.22/0.48          | ~ (l1_orders_2 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d5_lattice3])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k7_lattice3 @ X0)
% 0.22/0.48            = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 0.22/0.48               (u1_orders_2 @ (k3_waybel_9 @ X0))))
% 0.22/0.48          | ~ (l1_orders_2 @ X0)
% 0.22/0.48          | ~ (l1_orders_2 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X0)
% 0.22/0.48          | ((k7_lattice3 @ X0)
% 0.22/0.48              = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 0.22/0.48                 (u1_orders_2 @ (k3_waybel_9 @ X0)))))),
% 0.22/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X5 : $i]:
% 0.22/0.48         ((l1_waybel_0 @ (k3_waybel_9 @ X5) @ X5) | ~ (l1_orders_2 @ X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k3_waybel_9])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (v6_waybel_0 @ X3 @ X4)
% 0.22/0.48          | ~ (l1_waybel_0 @ X3 @ X4)
% 0.22/0.48          | ((X3) != (k3_waybel_9 @ X4))
% 0.22/0.48          | ((u1_struct_0 @ X3) = (u1_struct_0 @ X4))
% 0.22/0.48          | ~ (l1_orders_2 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [d6_waybel_9])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X4 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X4)
% 0.22/0.48          | ((u1_struct_0 @ (k3_waybel_9 @ X4)) = (u1_struct_0 @ X4))
% 0.22/0.48          | ~ (l1_waybel_0 @ (k3_waybel_9 @ X4) @ X4)
% 0.22/0.48          | ~ (v6_waybel_0 @ (k3_waybel_9 @ X4) @ X4))),
% 0.22/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X0)
% 0.22/0.48          | ~ (v6_waybel_0 @ (k3_waybel_9 @ X0) @ X0)
% 0.22/0.48          | ((u1_struct_0 @ (k3_waybel_9 @ X0)) = (u1_struct_0 @ X0))
% 0.22/0.48          | ~ (l1_orders_2 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((u1_struct_0 @ (k3_waybel_9 @ X0)) = (u1_struct_0 @ X0))
% 0.22/0.48          | ~ (v6_waybel_0 @ (k3_waybel_9 @ X0) @ X0)
% 0.22/0.48          | ~ (l1_orders_2 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X5 : $i]:
% 0.22/0.48         ((v6_waybel_0 @ (k3_waybel_9 @ X5) @ X5) | ~ (l1_orders_2 @ X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k3_waybel_9])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X0)
% 0.22/0.48          | ((u1_struct_0 @ (k3_waybel_9 @ X0)) = (u1_struct_0 @ X0)))),
% 0.22/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.22/0.48  thf(dt_k7_lattice3, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( ( v1_orders_2 @ ( k7_lattice3 @ A ) ) & 
% 0.22/0.48         ( l1_orders_2 @ ( k7_lattice3 @ A ) ) ) ))).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X2 : $i]: ((v1_orders_2 @ (k7_lattice3 @ X2)) | ~ (l1_orders_2 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k7_lattice3])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X2 : $i]: ((l1_orders_2 @ (k7_lattice3 @ X2)) | ~ (l1_orders_2 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k7_lattice3])).
% 0.22/0.48  thf(abstractness_v1_orders_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( ( v1_orders_2 @ A ) =>
% 0.22/0.48         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_orders_2 @ X0)
% 0.22/0.48          | ((X0) = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.22/0.48          | ~ (l1_orders_2 @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.22/0.48  thf(t11_waybel_9, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( ( g1_orders_2 @
% 0.22/0.48           ( u1_struct_0 @ ( k7_lattice3 @ A ) ) @ 
% 0.22/0.48           ( u1_orders_2 @ ( k7_lattice3 @ A ) ) ) =
% 0.22/0.48         ( g1_orders_2 @
% 0.22/0.48           ( u1_struct_0 @ ( k3_waybel_9 @ A ) ) @ 
% 0.22/0.48           ( u1_orders_2 @ ( k3_waybel_9 @ A ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( l1_orders_2 @ A ) =>
% 0.22/0.48          ( ( g1_orders_2 @
% 0.22/0.48              ( u1_struct_0 @ ( k7_lattice3 @ A ) ) @ 
% 0.22/0.48              ( u1_orders_2 @ ( k7_lattice3 @ A ) ) ) =
% 0.22/0.48            ( g1_orders_2 @
% 0.22/0.48              ( u1_struct_0 @ ( k3_waybel_9 @ A ) ) @ 
% 0.22/0.48              ( u1_orders_2 @ ( k3_waybel_9 @ A ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t11_waybel_9])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (((g1_orders_2 @ (u1_struct_0 @ (k7_lattice3 @ sk_A)) @ 
% 0.22/0.48         (u1_orders_2 @ (k7_lattice3 @ sk_A)))
% 0.22/0.48         != (g1_orders_2 @ (u1_struct_0 @ (k3_waybel_9 @ sk_A)) @ 
% 0.22/0.48             (u1_orders_2 @ (k3_waybel_9 @ sk_A))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      ((((k7_lattice3 @ sk_A)
% 0.22/0.48          != (g1_orders_2 @ (u1_struct_0 @ (k3_waybel_9 @ sk_A)) @ 
% 0.22/0.48              (u1_orders_2 @ (k3_waybel_9 @ sk_A))))
% 0.22/0.48        | ~ (l1_orders_2 @ (k7_lattice3 @ sk_A))
% 0.22/0.48        | ~ (v1_orders_2 @ (k7_lattice3 @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      ((~ (l1_orders_2 @ sk_A)
% 0.22/0.48        | ~ (v1_orders_2 @ (k7_lattice3 @ sk_A))
% 0.22/0.48        | ((k7_lattice3 @ sk_A)
% 0.22/0.48            != (g1_orders_2 @ (u1_struct_0 @ (k3_waybel_9 @ sk_A)) @ 
% 0.22/0.48                (u1_orders_2 @ (k3_waybel_9 @ sk_A)))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['18', '21'])).
% 0.22/0.48  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      ((~ (v1_orders_2 @ (k7_lattice3 @ sk_A))
% 0.22/0.48        | ((k7_lattice3 @ sk_A)
% 0.22/0.48            != (g1_orders_2 @ (u1_struct_0 @ (k3_waybel_9 @ sk_A)) @ 
% 0.22/0.48                (u1_orders_2 @ (k3_waybel_9 @ sk_A)))))),
% 0.22/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      ((~ (l1_orders_2 @ sk_A)
% 0.22/0.48        | ((k7_lattice3 @ sk_A)
% 0.22/0.48            != (g1_orders_2 @ (u1_struct_0 @ (k3_waybel_9 @ sk_A)) @ 
% 0.22/0.48                (u1_orders_2 @ (k3_waybel_9 @ sk_A)))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['17', '24'])).
% 0.22/0.48  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      (((k7_lattice3 @ sk_A)
% 0.22/0.48         != (g1_orders_2 @ (u1_struct_0 @ (k3_waybel_9 @ sk_A)) @ 
% 0.22/0.48             (u1_orders_2 @ (k3_waybel_9 @ sk_A))))),
% 0.22/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      ((((k7_lattice3 @ sk_A)
% 0.22/0.48          != (g1_orders_2 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48              (u1_orders_2 @ (k3_waybel_9 @ sk_A))))
% 0.22/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['16', '27'])).
% 0.22/0.48  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      (((k7_lattice3 @ sk_A)
% 0.22/0.48         != (g1_orders_2 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.48             (u1_orders_2 @ (k3_waybel_9 @ sk_A))))),
% 0.22/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      ((((k7_lattice3 @ sk_A) != (k7_lattice3 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '30'])).
% 0.22/0.48  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('33', plain, (((k7_lattice3 @ sk_A) != (k7_lattice3 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.48  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.35/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
