%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JzYKeSNd0J

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  77 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  267 ( 497 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xreal_0_type,type,(
    v1_xreal_0: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v1_xxreal_0_type,type,(
    v1_xxreal_0: $i > $o )).

thf(v1_xcmplx_0_type,type,(
    v1_xcmplx_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t6_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
              & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_yellow_0])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X10 @ X9 ) @ X10 )
      | ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A_1 )
      | ( r2_lattice3 @ sk_A_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_B_1 @ X0 @ sk_A_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_B_1 @ X0 @ sk_A_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A_1 @ X0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 )
    | ~ ( r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 )
   <= ~ ( r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X6 )
      | ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A_1 )
      | ( r1_lattice3 @ sk_A_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_A_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_A_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A_1 @ X0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 )
   <= ~ ( r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(rc4_xreal_0,axiom,(
    ? [A: $i] :
      ( ( v1_xreal_0 @ A )
      & ( v1_xxreal_0 @ A )
      & ( v1_xcmplx_0 @ A )
      & ( v1_xboole_0 @ A ) ) )).

thf('18',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc4_xreal_0])).

thf('19',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc4_xreal_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( ~ ( r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 )
    | ~ ( r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('25',plain,(
    ~ ( r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['8','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JzYKeSNd0J
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 42 iterations in 0.027s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v1_xreal_0_type, type, v1_xreal_0: $i > $o).
% 0.20/0.48  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.48  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.20/0.48  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.20/0.48  thf(v1_xxreal_0_type, type, v1_xxreal_0: $i > $o).
% 0.20/0.48  thf(v1_xcmplx_0_type, type, v1_xcmplx_0: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(t6_yellow_0, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.20/0.48             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_orders_2 @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.20/0.48                ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t6_yellow_0])).
% 0.20/0.48  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d9_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ![B:$i,C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.20/0.48             ( ![D:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.48          | (r2_hidden @ (sk_D_1 @ X8 @ X10 @ X9) @ X10)
% 0.20/0.48          | (r2_lattice3 @ X9 @ X10 @ X8)
% 0.20/0.48          | ~ (l1_orders_2 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_A_1)
% 0.20/0.48          | (r2_lattice3 @ sk_A_1 @ X0 @ sk_B_1)
% 0.20/0.48          | (r2_hidden @ (sk_D_1 @ sk_B_1 @ X0 @ sk_A_1) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain, ((l1_orders_2 @ sk_A_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_lattice3 @ sk_A_1 @ X0 @ sk_B_1)
% 0.20/0.48          | (r2_hidden @ (sk_D_1 @ sk_B_1 @ X0 @ sk_A_1) @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(d1_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_lattice3 @ sk_A_1 @ X0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((~ (r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1)
% 0.20/0.48        | ~ (r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((~ (r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1))
% 0.20/0.48         <= (~ ((r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['7'])).
% 0.20/0.48  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d8_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ![B:$i,C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.20/0.48             ( ![D:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.48          | (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X6)
% 0.20/0.48          | (r1_lattice3 @ X5 @ X6 @ X4)
% 0.20/0.48          | ~ (l1_orders_2 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_A_1)
% 0.20/0.48          | (r1_lattice3 @ sk_A_1 @ X0 @ sk_B_1)
% 0.20/0.48          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_A_1) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, ((l1_orders_2 @ sk_A_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_lattice3 @ sk_A_1 @ X0 @ sk_B_1)
% 0.20/0.48          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_A_1) @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_lattice3 @ sk_A_1 @ X0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((~ (r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1))
% 0.20/0.48         <= (~ ((r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['7'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.20/0.48         <= (~ ((r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf(rc4_xreal_0, axiom,
% 0.20/0.48    (?[A:$i]:
% 0.20/0.48     ( ( v1_xreal_0 @ A ) & ( v1_xxreal_0 @ A ) & ( v1_xcmplx_0 @ A ) & 
% 0.20/0.48       ( v1_xboole_0 @ A ) ))).
% 0.20/0.48  thf('18', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [rc4_xreal_0])).
% 0.20/0.48  thf('19', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [rc4_xreal_0])).
% 0.20/0.48  thf(l13_xboole_0, axiom,
% 0.20/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.48  thf('21', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.48  thf('23', plain, (((r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (~ ((r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1)) | 
% 0.20/0.48       ~ ((r1_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1))),
% 0.20/0.48      inference('split', [status(esa)], ['7'])).
% 0.20/0.48  thf('25', plain, (~ ((r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain, (~ (r2_lattice3 @ sk_A_1 @ k1_xboole_0 @ sk_B_1)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['8', '25'])).
% 0.20/0.48  thf('27', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '26'])).
% 0.20/0.48  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.48  thf('29', plain, ($false), inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
