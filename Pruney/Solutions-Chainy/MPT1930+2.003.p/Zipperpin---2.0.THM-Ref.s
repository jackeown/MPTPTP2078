%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rbZXfBcgmz

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  63 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  334 ( 712 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(t28_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
             => ( r2_waybel_0 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( r1_waybel_0 @ A @ B @ C )
               => ( r2_waybel_0 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_yellow_6])).

thf('0',plain,(
    ~ ( r2_waybel_0 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_waybel_0 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('3',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ( r1_waybel_0 @ X5 @ X4 @ ( k6_subset_1 @ ( u1_struct_0 @ X5 ) @ X6 ) )
      | ( r2_waybel_0 @ X5 @ X4 @ X6 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ( r1_waybel_0 @ X5 @ X4 @ ( k4_xboole_0 @ ( u1_struct_0 @ X5 ) @ X6 ) )
      | ( r2_waybel_0 @ X5 @ X4 @ X6 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t26_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ~ ( ( r1_waybel_0 @ A @ B @ C )
                & ( r1_waybel_0 @ A @ B @ D )
                & ( r1_xboole_0 @ C @ D ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( r1_waybel_0 @ X9 @ X8 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_6])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_waybel_0 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_waybel_0 @ sk_A @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rbZXfBcgmz
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 19 iterations in 0.016s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.44  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.44  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.44  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.21/0.44  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.44  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.44  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.44  thf(t28_yellow_6, conjecture,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.44       ( ![B:$i]:
% 0.21/0.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.44             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.44           ( ![C:$i]:
% 0.21/0.44             ( ( r1_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i]:
% 0.21/0.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.44          ( ![B:$i]:
% 0.21/0.44            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.44                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.44              ( ![C:$i]:
% 0.21/0.44                ( ( r1_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ C ) ) ) ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t28_yellow_6])).
% 0.21/0.44  thf('0', plain, (~ (r2_waybel_0 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('1', plain, ((r1_waybel_0 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(t79_xboole_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)),
% 0.21/0.44      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.44  thf('3', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(t10_waybel_0, axiom,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.44       ( ![B:$i]:
% 0.21/0.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.44           ( ![C:$i]:
% 0.21/0.44             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.44               ( ~( r1_waybel_0 @
% 0.21/0.44                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.21/0.44  thf('4', plain,
% 0.21/0.44      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.44         ((v2_struct_0 @ X4)
% 0.21/0.44          | ~ (l1_waybel_0 @ X4 @ X5)
% 0.21/0.44          | (r1_waybel_0 @ X5 @ X4 @ (k6_subset_1 @ (u1_struct_0 @ X5) @ X6))
% 0.21/0.44          | (r2_waybel_0 @ X5 @ X4 @ X6)
% 0.21/0.44          | ~ (l1_struct_0 @ X5)
% 0.21/0.44          | (v2_struct_0 @ X5))),
% 0.21/0.44      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.21/0.44  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.44  thf('5', plain,
% 0.21/0.44      (![X2 : $i, X3 : $i]: ((k6_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))),
% 0.21/0.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.44  thf('6', plain,
% 0.21/0.44      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.44         ((v2_struct_0 @ X4)
% 0.21/0.44          | ~ (l1_waybel_0 @ X4 @ X5)
% 0.21/0.44          | (r1_waybel_0 @ X5 @ X4 @ (k4_xboole_0 @ (u1_struct_0 @ X5) @ X6))
% 0.21/0.44          | (r2_waybel_0 @ X5 @ X4 @ X6)
% 0.21/0.44          | ~ (l1_struct_0 @ X5)
% 0.21/0.44          | (v2_struct_0 @ X5))),
% 0.21/0.44      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.44  thf('7', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         ((v2_struct_0 @ sk_A)
% 0.21/0.44          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.44          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.44          | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.44             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.44          | (v2_struct_0 @ sk_B))),
% 0.21/0.44      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.44  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('9', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         ((v2_struct_0 @ sk_A)
% 0.21/0.44          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.44          | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.44             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.44          | (v2_struct_0 @ sk_B))),
% 0.21/0.44      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.44  thf(t26_yellow_6, axiom,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.44       ( ![B:$i]:
% 0.21/0.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.44             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.44           ( ![C:$i,D:$i]:
% 0.21/0.44             ( ~( ( r1_waybel_0 @ A @ B @ C ) & ( r1_waybel_0 @ A @ B @ D ) & 
% 0.21/0.44                  ( r1_xboole_0 @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.44  thf('10', plain,
% 0.21/0.44      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.44         ((v2_struct_0 @ X8)
% 0.21/0.44          | ~ (v4_orders_2 @ X8)
% 0.21/0.44          | ~ (v7_waybel_0 @ X8)
% 0.21/0.44          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.21/0.44          | ~ (r1_waybel_0 @ X9 @ X8 @ X10)
% 0.21/0.44          | ~ (r1_xboole_0 @ X10 @ X11)
% 0.21/0.44          | ~ (r1_waybel_0 @ X9 @ X8 @ X11)
% 0.21/0.44          | ~ (l1_struct_0 @ X9)
% 0.21/0.44          | (v2_struct_0 @ X9))),
% 0.21/0.44      inference('cnf', [status(esa)], [t26_yellow_6])).
% 0.21/0.44  thf('11', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         ((v2_struct_0 @ sk_B)
% 0.21/0.44          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.44          | (v2_struct_0 @ sk_A)
% 0.21/0.44          | (v2_struct_0 @ sk_A)
% 0.21/0.44          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.44          | ~ (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.21/0.44          | ~ (r1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.21/0.44          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.44          | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.44          | ~ (v4_orders_2 @ sk_B)
% 0.21/0.44          | (v2_struct_0 @ sk_B))),
% 0.21/0.44      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.44  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('13', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('14', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('15', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('16', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         ((v2_struct_0 @ sk_B)
% 0.21/0.44          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.44          | (v2_struct_0 @ sk_A)
% 0.21/0.44          | (v2_struct_0 @ sk_A)
% 0.21/0.44          | ~ (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.21/0.44          | ~ (r1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.21/0.44          | (v2_struct_0 @ sk_B))),
% 0.21/0.44      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.21/0.44  thf('17', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (~ (r1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.21/0.44          | ~ (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.21/0.44          | (v2_struct_0 @ sk_A)
% 0.21/0.44          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.44          | (v2_struct_0 @ sk_B))),
% 0.21/0.44      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.44  thf('18', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         ((v2_struct_0 @ sk_B)
% 0.21/0.44          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.44          | (v2_struct_0 @ sk_A)
% 0.21/0.44          | ~ (r1_waybel_0 @ sk_A @ sk_B @ X0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['2', '17'])).
% 0.21/0.44  thf('19', plain,
% 0.21/0.44      (((v2_struct_0 @ sk_A)
% 0.21/0.44        | (r2_waybel_0 @ sk_A @ sk_B @ sk_C)
% 0.21/0.44        | (v2_struct_0 @ sk_B))),
% 0.21/0.44      inference('sup-', [status(thm)], ['1', '18'])).
% 0.21/0.44  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('21', plain,
% 0.21/0.44      (((v2_struct_0 @ sk_B) | (r2_waybel_0 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.44      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.44  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('23', plain, ((r2_waybel_0 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.44      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.44  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
