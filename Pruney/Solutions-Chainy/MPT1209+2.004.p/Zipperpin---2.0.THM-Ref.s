%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lcFKsDvIxM

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  82 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  418 ( 839 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(t44_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B )
            = ( k6_lattices @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v14_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B )
              = ( k6_lattices @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l2_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ~ ( v4_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k3_lattices @ X7 @ X6 @ X8 )
        = ( k1_lattices @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 ) )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
      = ( k1_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B ) )
    | ~ ( v4_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( l2_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('9',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l2_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf(d17_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( ( v14_lattices @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( B
                = ( k6_lattices @ A ) )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( ( k1_lattices @ A @ B @ C )
                      = B )
                    & ( ( k1_lattices @ A @ C @ B )
                      = B ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v14_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( X2
       != ( k6_lattices @ X1 ) )
      | ( ( k1_lattices @ X1 @ X2 @ X3 )
        = X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d17_lattices])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l2_lattices @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_lattices @ X1 @ ( k6_lattices @ X1 ) @ X3 )
        = ( k6_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ ( k6_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v14_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( ( k1_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 )
        = ( k6_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 )
        = ( k6_lattices @ X0 ) )
      | ~ ( v14_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
      = ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,(
    v14_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','9','21','27'])).

thf('29',plain,(
    ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
 != ( k6_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lcFKsDvIxM
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:51:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 57 iterations in 0.047s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.51  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.51  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 0.21/0.51  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.51  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.51  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.51  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.21/0.51  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 0.21/0.51  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.51  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.51  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.51  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.51  thf(t44_lattices, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B ) =
% 0.21/0.51             ( k6_lattices @ A ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51            ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51              ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B ) =
% 0.21/0.51                ( k6_lattices @ A ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t44_lattices])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k6_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X4 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k6_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.21/0.51          | ~ (l2_lattices @ X4)
% 0.21/0.51          | (v2_struct_0 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.21/0.51  thf(redefinition_k3_lattices, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.51         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.21/0.51          | ~ (l2_lattices @ X7)
% 0.21/0.51          | ~ (v4_lattices @ X7)
% 0.21/0.51          | (v2_struct_0 @ X7)
% 0.21/0.51          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.21/0.51          | ((k3_lattices @ X7 @ X6 @ X8) = (k1_lattices @ X7 @ X6 @ X8)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l2_lattices @ X0)
% 0.21/0.51          | ((k3_lattices @ X0 @ (k6_lattices @ X0) @ X1)
% 0.21/0.51              = (k1_lattices @ X0 @ (k6_lattices @ X0) @ X1))
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v4_lattices @ X0)
% 0.21/0.51          | ~ (l2_lattices @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v4_lattices @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ((k3_lattices @ X0 @ (k6_lattices @ X0) @ X1)
% 0.21/0.51              = (k1_lattices @ X0 @ (k6_lattices @ X0) @ X1))
% 0.21/0.51          | ~ (l2_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l2_lattices @ sk_A)
% 0.21/0.51        | ((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)
% 0.21/0.51            = (k1_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B))
% 0.21/0.51        | ~ (v4_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '5'])).
% 0.21/0.51  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l3_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.51  thf('8', plain, (![X5 : $i]: ((l2_lattices @ X5) | ~ (l3_lattices @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.51  thf('9', plain, ((l2_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X4 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k6_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.21/0.51          | ~ (l2_lattices @ X4)
% 0.21/0.51          | (v2_struct_0 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.21/0.51  thf(d17_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.51       ( ( v14_lattices @ A ) =>
% 0.21/0.51         ( ![B:$i]:
% 0.21/0.51           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51             ( ( ( B ) = ( k6_lattices @ A ) ) <=>
% 0.21/0.51               ( ![C:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                   ( ( ( k1_lattices @ A @ B @ C ) = ( B ) ) & 
% 0.21/0.51                     ( ( k1_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (v14_lattices @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ((X2) != (k6_lattices @ X1))
% 0.21/0.51          | ((k1_lattices @ X1 @ X2 @ X3) = (X2))
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (l2_lattices @ X1)
% 0.21/0.51          | (v2_struct_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d17_lattices])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X1)
% 0.21/0.51          | ~ (l2_lattices @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ((k1_lattices @ X1 @ (k6_lattices @ X1) @ X3) = (k6_lattices @ X1))
% 0.21/0.51          | ~ (m1_subset_1 @ (k6_lattices @ X1) @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (v14_lattices @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l2_lattices @ X0)
% 0.21/0.51          | ~ (v14_lattices @ X0)
% 0.21/0.51          | ((k1_lattices @ X0 @ (k6_lattices @ X0) @ X1) = (k6_lattices @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l2_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ((k1_lattices @ X0 @ (k6_lattices @ X0) @ X1) = (k6_lattices @ X0))
% 0.21/0.51          | ~ (v14_lattices @ X0)
% 0.21/0.51          | ~ (l2_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l2_lattices @ sk_A)
% 0.21/0.51        | ~ (v14_lattices @ sk_A)
% 0.21/0.51        | ((k1_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)
% 0.21/0.51            = (k6_lattices @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '15'])).
% 0.21/0.51  thf('17', plain, ((l2_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('18', plain, ((v14_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k1_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)
% 0.21/0.51            = (k6_lattices @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.51  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (((k1_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)
% 0.21/0.51         = (k6_lattices @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf(cc1_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l3_lattices @ A ) =>
% 0.21/0.51       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.51         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.51           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.51           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v10_lattices @ X0)
% 0.21/0.51          | (v4_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.51  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain, ((v4_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)
% 0.21/0.51            = (k6_lattices @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '9', '21', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)
% 0.21/0.51         != (k6_lattices @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
