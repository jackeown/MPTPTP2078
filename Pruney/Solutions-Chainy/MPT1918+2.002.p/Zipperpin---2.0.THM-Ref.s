%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1lCYqZWq3e

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 152 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  303 (1099 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t16_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ! [C: $i] :
              ( ( m1_yellow_0 @ C @ B )
             => ( m1_yellow_0 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_yellow_0 @ B @ A )
           => ! [C: $i] :
                ( ( m1_yellow_0 @ C @ B )
               => ( m1_yellow_0 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_yellow_6])).

thf('0',plain,(
    ~ ( m1_yellow_0 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( m1_yellow_0 @ B @ A )
          <=> ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
              & ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_orders_2 @ X3 )
      | ~ ( m1_yellow_0 @ X3 @ X4 )
      | ( r1_tarski @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('3',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_yellow_0 @ X5 @ X6 )
      | ( l1_orders_2 @ X5 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_0])).

thf('7',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','9'])).

thf('11',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_orders_2 @ X3 )
      | ~ ( m1_yellow_0 @ X3 @ X4 )
      | ( r1_tarski @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('13',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('15',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_yellow_0 @ X5 @ X6 )
      | ( l1_orders_2 @ X5 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_0])).

thf('17',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','19'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_orders_2 @ X3 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_tarski @ ( u1_orders_2 @ X3 ) @ ( u1_orders_2 @ X4 ) )
      | ( m1_yellow_0 @ X3 @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('25',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_yellow_0 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_orders_2 @ X3 )
      | ~ ( m1_yellow_0 @ X3 @ X4 )
      | ( r1_tarski @ ( u1_orders_2 @ X3 ) @ ( u1_orders_2 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('29',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_tarski @ ( u1_orders_2 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('32',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_orders_2 @ X3 )
      | ~ ( m1_yellow_0 @ X3 @ X4 )
      | ( r1_tarski @ ( u1_orders_2 @ X3 ) @ ( u1_orders_2 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('35',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('37',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('38',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_orders_2 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ ( u1_orders_2 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('43',plain,(
    m1_yellow_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['25','26','41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1lCYqZWq3e
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:50:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 23 iterations in 0.014s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.49  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.49  thf(t16_yellow_6, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_yellow_0 @ B @ A ) =>
% 0.21/0.49           ( ![C:$i]: ( ( m1_yellow_0 @ C @ B ) => ( m1_yellow_0 @ C @ A ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( l1_orders_2 @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_yellow_0 @ B @ A ) =>
% 0.21/0.49              ( ![C:$i]: ( ( m1_yellow_0 @ C @ B ) => ( m1_yellow_0 @ C @ A ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t16_yellow_6])).
% 0.21/0.49  thf('0', plain, (~ (m1_yellow_0 @ sk_C @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, ((m1_yellow_0 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d13_yellow_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_orders_2 @ B ) =>
% 0.21/0.49           ( ( m1_yellow_0 @ B @ A ) <=>
% 0.21/0.49             ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.49               ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ X3)
% 0.21/0.49          | ~ (m1_yellow_0 @ X3 @ X4)
% 0.21/0.49          | (r1_tarski @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X4))
% 0.21/0.49          | ~ (l1_orders_2 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.49        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (l1_orders_2 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, ((m1_yellow_0 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_m1_yellow_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ A ) =>
% 0.21/0.49       ( ![B:$i]: ( ( m1_yellow_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (m1_yellow_0 @ X5 @ X6) | (l1_orders_2 @ X5) | ~ (l1_orders_2 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_yellow_0])).
% 0.21/0.49  thf('7', plain, ((~ (l1_orders_2 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4', '9'])).
% 0.21/0.49  thf('11', plain, ((m1_yellow_0 @ sk_C @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ X3)
% 0.21/0.49          | ~ (m1_yellow_0 @ X3 @ X4)
% 0.21/0.49          | (r1_tarski @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X4))
% 0.21/0.49          | ~ (l1_orders_2 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((~ (l1_orders_2 @ sk_B)
% 0.21/0.49        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.21/0.49        | ~ (l1_orders_2 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('15', plain, ((m1_yellow_0 @ sk_C @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (m1_yellow_0 @ X5 @ X6) | (l1_orders_2 @ X5) | ~ (l1_orders_2 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_yellow_0])).
% 0.21/0.49  thf('17', plain, ((~ (l1_orders_2 @ sk_B) | (l1_orders_2 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('19', plain, ((l1_orders_2 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14', '19'])).
% 0.21/0.49  thf(t1_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.49       ( r1_tarski @ A @ C ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.49          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.49          | (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ (u1_struct_0 @ sk_C) @ X0)
% 0.21/0.49          | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ X3)
% 0.21/0.49          | ~ (r1_tarski @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X4))
% 0.21/0.49          | ~ (r1_tarski @ (u1_orders_2 @ X3) @ (u1_orders_2 @ X4))
% 0.21/0.49          | (m1_yellow_0 @ X3 @ X4)
% 0.21/0.49          | ~ (l1_orders_2 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.49        | (m1_yellow_0 @ sk_C @ sk_A)
% 0.21/0.49        | ~ (r1_tarski @ (u1_orders_2 @ sk_C) @ (u1_orders_2 @ sk_A))
% 0.21/0.49        | ~ (l1_orders_2 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, ((m1_yellow_0 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ X3)
% 0.21/0.49          | ~ (m1_yellow_0 @ X3 @ X4)
% 0.21/0.49          | (r1_tarski @ (u1_orders_2 @ X3) @ (u1_orders_2 @ X4))
% 0.21/0.49          | ~ (l1_orders_2 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.49        | (r1_tarski @ (u1_orders_2 @ sk_B) @ (u1_orders_2 @ sk_A))
% 0.21/0.49        | ~ (l1_orders_2 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('32', plain, ((r1_tarski @ (u1_orders_2 @ sk_B) @ (u1_orders_2 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.49  thf('33', plain, ((m1_yellow_0 @ sk_C @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ X3)
% 0.21/0.49          | ~ (m1_yellow_0 @ X3 @ X4)
% 0.21/0.49          | (r1_tarski @ (u1_orders_2 @ X3) @ (u1_orders_2 @ X4))
% 0.21/0.49          | ~ (l1_orders_2 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((~ (l1_orders_2 @ sk_B)
% 0.21/0.49        | (r1_tarski @ (u1_orders_2 @ sk_C) @ (u1_orders_2 @ sk_B))
% 0.21/0.49        | ~ (l1_orders_2 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('37', plain, ((l1_orders_2 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('38', plain, ((r1_tarski @ (u1_orders_2 @ sk_C) @ (u1_orders_2 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.49          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.49          | (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ (u1_orders_2 @ sk_C) @ X0)
% 0.21/0.49          | ~ (r1_tarski @ (u1_orders_2 @ sk_B) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain, ((r1_tarski @ (u1_orders_2 @ sk_C) @ (u1_orders_2 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '40'])).
% 0.21/0.49  thf('42', plain, ((l1_orders_2 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('43', plain, ((m1_yellow_0 @ sk_C @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26', '41', '42'])).
% 0.21/0.49  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
