%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q4kshpFpPW

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  258 ( 451 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ( r1_lattice3 @ X4 @ X5 @ X3 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,
    ( ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X9 @ X8 ) @ X9 )
      | ( r2_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['15','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q4kshpFpPW
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:12:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 44 iterations in 0.031s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.21/0.49  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.21/0.49  thf(t6_yellow_0, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.21/0.49             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( l1_orders_2 @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49              ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.21/0.49                ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t6_yellow_0])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 0.21/0.49        | ~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))
% 0.21/0.49         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.49  thf('2', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.49  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d8_lattice3, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ A ) =>
% 0.21/0.49       ( ![B:$i,C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.21/0.49             ( ![D:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.21/0.49          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.21/0.49          | (r1_lattice3 @ X4 @ X5 @ X3)
% 0.21/0.49          | ~ (l1_orders_2 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.21/0.49          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.21/0.49          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(t7_ordinal1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i]: (~ (r2_hidden @ X1 @ X2) | ~ (r1_tarski @ X2 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.21/0.49          | ~ (r1_tarski @ X0 @ (sk_D @ sk_B @ X0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))
% 0.21/0.49         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('12', plain, (((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)) | 
% 0.21/0.49       ~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('14', plain, (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain, (~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['1', '14'])).
% 0.21/0.49  thf('16', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.49  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d9_lattice3, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ A ) =>
% 0.21/0.49       ( ![B:$i,C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.21/0.49             ( ![D:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.49          | (r2_hidden @ (sk_D_1 @ X7 @ X9 @ X8) @ X9)
% 0.21/0.49          | (r2_lattice3 @ X8 @ X9 @ X7)
% 0.21/0.49          | ~ (l1_orders_2 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.21/0.49          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.21/0.49          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i]: (~ (r2_hidden @ X1 @ X2) | ~ (r1_tarski @ X2 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.21/0.49          | ~ (r1_tarski @ X0 @ (sk_D_1 @ sk_B @ X0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '23'])).
% 0.21/0.49  thf('25', plain, ($false), inference('demod', [status(thm)], ['15', '24'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
