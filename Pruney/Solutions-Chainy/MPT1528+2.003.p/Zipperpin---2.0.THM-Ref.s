%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9PrZbIk2fW

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 ( 435 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X9 @ X8 ) @ X9 )
      | ( r2_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_B_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_B_1 @ X0 @ sk_A ) @ X0 ) ) ),
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
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 )
    | ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ( r1_lattice3 @ X4 @ X5 @ X3 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 )
    | ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('21',plain,(
    ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['8','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9PrZbIk2fW
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:22:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 43 iterations in 0.031s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.22/0.49  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.49  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.22/0.49  thf(t6_yellow_0, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_orders_2 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.22/0.49             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( l1_orders_2 @ A ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49              ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.22/0.49                ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t6_yellow_0])).
% 0.22/0.49  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d9_lattice3, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_orders_2 @ A ) =>
% 0.22/0.49       ( ![B:$i,C:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.22/0.49             ( ![D:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.22/0.49          | (r2_hidden @ (sk_D_1 @ X7 @ X9 @ X8) @ X9)
% 0.22/0.49          | (r2_lattice3 @ X8 @ X9 @ X7)
% 0.22/0.49          | ~ (l1_orders_2 @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_orders_2 @ sk_A)
% 0.22/0.49          | (r2_lattice3 @ sk_A @ X0 @ sk_B_1)
% 0.22/0.49          | (r2_hidden @ (sk_D_1 @ sk_B_1 @ X0 @ sk_A) @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_lattice3 @ sk_A @ X0 @ sk_B_1)
% 0.22/0.49          | (r2_hidden @ (sk_D_1 @ sk_B_1 @ X0 @ sk_A) @ X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(d1_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i]: ((r2_lattice3 @ sk_A @ X0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)
% 0.22/0.49        | ~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))
% 0.22/0.49         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.22/0.49      inference('split', [status(esa)], ['7'])).
% 0.22/0.49  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d8_lattice3, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_orders_2 @ A ) =>
% 0.22/0.49       ( ![B:$i,C:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.22/0.49             ( ![D:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.22/0.49          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.22/0.49          | (r1_lattice3 @ X4 @ X5 @ X3)
% 0.22/0.49          | ~ (l1_orders_2 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_orders_2 @ sk_A)
% 0.22/0.49          | (r1_lattice3 @ sk_A @ X0 @ sk_B_1)
% 0.22/0.49          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_A) @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_lattice3 @ sk_A @ X0 @ sk_B_1)
% 0.22/0.49          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_A) @ X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X0 : $i]: ((r1_lattice3 @ sk_A @ X0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      ((~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))
% 0.22/0.49         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.22/0.49      inference('split', [status(esa)], ['7'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.22/0.49         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.49  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.49  thf('19', plain, (((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)) | 
% 0.22/0.49       ~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.22/0.49      inference('split', [status(esa)], ['7'])).
% 0.22/0.49  thf('21', plain, (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain, (~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['8', '21'])).
% 0.22/0.49  thf('23', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '22'])).
% 0.22/0.49  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.49  thf('25', plain, ($false), inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
