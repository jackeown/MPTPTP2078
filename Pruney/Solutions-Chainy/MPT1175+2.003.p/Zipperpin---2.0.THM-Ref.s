%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7t4OVPV98C

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  83 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  259 (1084 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

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
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_orders_1 @ X9 @ ( k1_orders_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ ( u1_struct_0 @ X10 ) ) @ X11 )
      | ~ ( m2_orders_2 @ X11 @ X10 @ X9 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_C ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_D_1 )
    = sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    m2_orders_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('21',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['18','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7t4OVPV98C
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 20 iterations in 0.014s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.45  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.45  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.45  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.45  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.45  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.45  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.45  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.45  thf(t82_orders_2, conjecture,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.45         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.45           ( ![C:$i]:
% 0.20/0.45             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.45               ( ![D:$i]:
% 0.20/0.45                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i]:
% 0.20/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.45            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.45          ( ![B:$i]:
% 0.20/0.45            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.45              ( ![C:$i]:
% 0.20/0.45                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.45                  ( ![D:$i]:
% 0.20/0.45                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.45                      ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t82_orders_2])).
% 0.20/0.45  thf('0', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t79_orders_2, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.45         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.45           ( ![C:$i]:
% 0.20/0.45             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.45               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.45         (~ (m1_orders_1 @ X9 @ (k1_orders_1 @ (u1_struct_0 @ X10)))
% 0.20/0.45          | (r2_hidden @ (k1_funct_1 @ X9 @ (u1_struct_0 @ X10)) @ X11)
% 0.20/0.45          | ~ (m2_orders_2 @ X11 @ X10 @ X9)
% 0.20/0.45          | ~ (l1_orders_2 @ X10)
% 0.20/0.45          | ~ (v5_orders_2 @ X10)
% 0.20/0.45          | ~ (v4_orders_2 @ X10)
% 0.20/0.45          | ~ (v3_orders_2 @ X10)
% 0.20/0.45          | (v2_struct_0 @ X10))),
% 0.20/0.45      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_A)
% 0.20/0.45          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.45          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.45          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.45          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.45          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.45  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('5', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_A)
% 0.20/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.45          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.45      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.20/0.45  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.45      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_C)),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '10'])).
% 0.20/0.45  thf('12', plain, ((r1_xboole_0 @ sk_C @ sk_D_1)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t83_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X6 : $i, X7 : $i]:
% 0.20/0.45         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.20/0.45      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.45  thf('14', plain, (((k4_xboole_0 @ sk_C @ sk_D_1) = (sk_C))),
% 0.20/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf(d5_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.45       ( ![D:$i]:
% 0.20/0.45         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.45           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.45          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.45          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.45          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.45  thf('17', plain,
% 0.20/0.45      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.20/0.45      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.45  thf('18', plain,
% 0.20/0.45      (~ (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_D_1)),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '17'])).
% 0.20/0.45  thf('19', plain, ((m2_orders_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('20', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.45      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_D_1)),
% 0.20/0.45      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.45  thf('22', plain, ($false), inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
