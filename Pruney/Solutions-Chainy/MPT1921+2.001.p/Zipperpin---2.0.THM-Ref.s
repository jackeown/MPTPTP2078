%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vv4hv1tSDA

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  78 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  237 ( 621 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t19_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ! [C: $i] :
              ( ( m1_yellow_6 @ C @ A @ B )
             => ( r1_tarski @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_waybel_0 @ B @ A )
           => ! [C: $i] :
                ( ( m1_yellow_6 @ C @ A @ B )
               => ( r1_tarski @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_yellow_6])).

thf('0',plain,(
    ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ! [C: $i] :
              ( ( l1_waybel_0 @ C @ A )
             => ( ( m1_yellow_6 @ C @ A @ B )
              <=> ( ( m1_yellow_0 @ C @ B )
                  & ( ( u1_waybel_0 @ A @ C )
                    = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_waybel_0 @ X4 @ X5 )
      | ~ ( m1_yellow_6 @ X6 @ X5 @ X4 )
      | ( m1_yellow_0 @ X6 @ X4 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('3',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( m1_yellow_0 @ sk_C @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( m1_yellow_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_yellow_6 @ C @ A @ B )
         => ( l1_waybel_0 @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ~ ( l1_waybel_0 @ X8 @ X7 )
      | ( l1_waybel_0 @ X9 @ X7 )
      | ~ ( m1_yellow_6 @ X9 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_6])).

thf('9',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['6','12'])).

thf(d13_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( m1_yellow_0 @ B @ A )
          <=> ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
              & ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_yellow_0 @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('15',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_waybel_0 @ X2 @ X3 )
      | ( l1_orders_2 @ X2 )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('18',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_waybel_0 @ X2 @ X3 )
      | ( l1_orders_2 @ X2 )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('23',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','20','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vv4hv1tSDA
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:34:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 17 iterations in 0.014s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.46  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.19/0.46  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.19/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.46  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.19/0.46  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.46  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(m1_yellow_6_type, type, m1_yellow_6: $i > $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(t19_yellow_6, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_struct_0 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( l1_waybel_0 @ B @ A ) =>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.19/0.46               ( r1_tarski @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( l1_struct_0 @ A ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( l1_waybel_0 @ B @ A ) =>
% 0.19/0.46              ( ![C:$i]:
% 0.19/0.46                ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.19/0.46                  ( r1_tarski @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t19_yellow_6])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d8_yellow_6, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_struct_0 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( l1_waybel_0 @ B @ A ) =>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( l1_waybel_0 @ C @ A ) =>
% 0.19/0.46               ( ( m1_yellow_6 @ C @ A @ B ) <=>
% 0.19/0.46                 ( ( m1_yellow_0 @ C @ B ) & 
% 0.19/0.46                   ( ( u1_waybel_0 @ A @ C ) =
% 0.19/0.46                     ( k2_partfun1 @
% 0.19/0.46                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.46                       ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.46         (~ (l1_waybel_0 @ X4 @ X5)
% 0.19/0.46          | ~ (m1_yellow_6 @ X6 @ X5 @ X4)
% 0.19/0.46          | (m1_yellow_0 @ X6 @ X4)
% 0.19/0.46          | ~ (l1_waybel_0 @ X6 @ X5)
% 0.19/0.46          | ~ (l1_struct_0 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.46        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.19/0.46        | (m1_yellow_0 @ sk_C @ sk_B)
% 0.19/0.46        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('5', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      ((~ (l1_waybel_0 @ sk_C @ sk_A) | (m1_yellow_0 @ sk_C @ sk_B))),
% 0.19/0.46      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.46  thf('7', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(dt_m1_yellow_6, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.46       ( ![C:$i]: ( ( m1_yellow_6 @ C @ A @ B ) => ( l1_waybel_0 @ C @ A ) ) ) ))).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.46         (~ (l1_struct_0 @ X7)
% 0.19/0.46          | ~ (l1_waybel_0 @ X8 @ X7)
% 0.19/0.46          | (l1_waybel_0 @ X9 @ X7)
% 0.19/0.46          | ~ (m1_yellow_6 @ X9 @ X7 @ X8))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_m1_yellow_6])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (((l1_waybel_0 @ sk_C @ sk_A)
% 0.19/0.46        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.19/0.46        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('12', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.19/0.46  thf('13', plain, ((m1_yellow_0 @ sk_C @ sk_B)),
% 0.19/0.46      inference('demod', [status(thm)], ['6', '12'])).
% 0.19/0.46  thf(d13_yellow_0, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_orders_2 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( l1_orders_2 @ B ) =>
% 0.19/0.46           ( ( m1_yellow_0 @ B @ A ) <=>
% 0.19/0.46             ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.46               ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ))).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (l1_orders_2 @ X0)
% 0.19/0.46          | ~ (m1_yellow_0 @ X0 @ X1)
% 0.19/0.46          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.19/0.46          | ~ (l1_orders_2 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      ((~ (l1_orders_2 @ sk_B)
% 0.19/0.46        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.19/0.46        | ~ (l1_orders_2 @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.46  thf('16', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(dt_l1_waybel_0, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_struct_0 @ A ) =>
% 0.19/0.46       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (l1_waybel_0 @ X2 @ X3) | (l1_orders_2 @ X2) | ~ (l1_struct_0 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.19/0.46  thf('18', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.46  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('20', plain, ((l1_orders_2 @ sk_B)),
% 0.19/0.46      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.46  thf('21', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (l1_waybel_0 @ X2 @ X3) | (l1_orders_2 @ X2) | ~ (l1_struct_0 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.19/0.46  thf('23', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.46  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('25', plain, ((l1_orders_2 @ sk_C)),
% 0.19/0.46      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.46  thf('26', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.19/0.46      inference('demod', [status(thm)], ['15', '20', '25'])).
% 0.19/0.46  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
