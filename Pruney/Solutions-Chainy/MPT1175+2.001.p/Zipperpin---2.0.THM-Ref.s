%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ib50n5pztY

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  98 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  322 (1270 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(t82_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ~ ( r1_xboole_0 @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m2_orders_2 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m2_orders_2 @ D @ A @ B )
                   => ~ ( r1_xboole_0 @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_orders_2])).

thf('0',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X13 @ ( u1_struct_0 @ X14 ) ) @ X15 )
      | ~ ( m2_orders_2 @ X15 @ X14 @ X13 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    m2_orders_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('14',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference('sup-',[status(thm)],['22','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ib50n5pztY
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:36:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 124 iterations in 0.057s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.52  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.52  thf(t82_orders_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.52                      ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t82_orders_2])).
% 0.20/0.52  thf('0', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t79_orders_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ X13 @ (u1_struct_0 @ X14)) @ X15)
% 0.20/0.52          | ~ (m2_orders_2 @ X15 @ X14 @ X13)
% 0.20/0.52          | ~ (l1_orders_2 @ X14)
% 0.20/0.52          | ~ (v5_orders_2 @ X14)
% 0.20/0.52          | ~ (v4_orders_2 @ X14)
% 0.20/0.52          | ~ (v3_orders_2 @ X14)
% 0.20/0.52          | (v2_struct_0 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.20/0.52  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_C_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '10'])).
% 0.20/0.52  thf('12', plain, ((m2_orders_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_D_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf(d4_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ X2)
% 0.20/0.52          | (r2_hidden @ X0 @ X3)
% 0.20/0.52          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.52             (k3_xboole_0 @ X0 @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.52        (k3_xboole_0 @ sk_C_1 @ sk_D_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '17'])).
% 0.20/0.52  thf('19', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d7_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.52  thf('21', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D_1) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ k1_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.52  thf('23', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D_1) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf(t4_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.20/0.52          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_C_1 @ sk_D_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain, ($false), inference('sup-', [status(thm)], ['22', '27'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
