%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o7Ig2w7TR1

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  263 ( 493 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X12 @ X11 ) @ X12 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('24',plain,(
    r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['17','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o7Ig2w7TR1
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 42 iterations in 0.030s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.19/0.48  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(t6_yellow_0, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_orders_2 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.19/0.48             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( l1_orders_2 @ A ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48              ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.19/0.48                ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t6_yellow_0])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 0.19/0.48        | ~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))
% 0.19/0.48         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d8_lattice3, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_orders_2 @ A ) =>
% 0.19/0.48       ( ![B:$i,C:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.19/0.48             ( ![D:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.19/0.48          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 0.19/0.48          | (r1_lattice3 @ X7 @ X8 @ X6)
% 0.19/0.48          | ~ (l1_orders_2 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_orders_2 @ sk_A)
% 0.19/0.48          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.19/0.48          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.19/0.48          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf(t2_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.48  thf(t4_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.19/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.48  thf('10', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.48  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain, ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))
% 0.19/0.48         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('14', plain, (((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)) | 
% 0.19/0.48       ~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('16', plain, (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('17', plain, (~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.19/0.48  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d9_lattice3, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_orders_2 @ A ) =>
% 0.19/0.48       ( ![B:$i,C:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.19/0.48             ( ![D:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.19/0.48          | (r2_hidden @ (sk_D_1 @ X10 @ X12 @ X11) @ X12)
% 0.19/0.48          | (r2_lattice3 @ X11 @ X12 @ X10)
% 0.19/0.48          | ~ (l1_orders_2 @ X11))),
% 0.19/0.48      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_orders_2 @ sk_A)
% 0.19/0.48          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.19/0.48          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.19/0.48          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('23', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('24', plain, ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain, ($false), inference('demod', [status(thm)], ['17', '24'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
