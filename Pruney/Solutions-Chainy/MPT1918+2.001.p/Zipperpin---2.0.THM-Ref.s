%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZlIXHoP9rK

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:54 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 175 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  443 (1293 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('1',plain,(
    m1_yellow_0 @ sk_C_1 @ sk_B ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_yellow_0 @ X4 @ X5 )
      | ( r1_tarski @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('3',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_yellow_0 @ X6 @ X7 )
      | ( l1_orders_2 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_0])).

thf('6',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_yellow_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_yellow_0 @ X6 @ X7 )
      | ( l1_orders_2 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_0])).

thf('11',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( l1_orders_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('13',plain,(
    l1_orders_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_yellow_0 @ X4 @ X5 )
      | ( r1_tarski @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('20',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('23',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_tarski @ ( u1_orders_2 @ X4 ) @ ( u1_orders_2 @ X5 ) )
      | ( m1_yellow_0 @ X4 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('31',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_yellow_0 @ sk_C_1 @ sk_A )
    | ~ ( r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_orders_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('34',plain,
    ( ( m1_yellow_0 @ sk_C_1 @ sk_A )
    | ~ ( r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( m1_yellow_0 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    m1_yellow_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_yellow_0 @ X4 @ X5 )
      | ( r1_tarski @ ( u1_orders_2 @ X4 ) @ ( u1_orders_2 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('40',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('42',plain,(
    l1_orders_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('43',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_orders_2 @ sk_C_1 ) ) @ ( u1_orders_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_yellow_0 @ X4 @ X5 )
      | ( r1_tarski @ ( u1_orders_2 @ X4 ) @ ( u1_orders_2 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('49',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_tarski @ ( u1_orders_2 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('52',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_orders_2 @ sk_C_1 ) ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,
    ( ( r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ( r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['36','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZlIXHoP9rK
% 0.11/0.31  % Computer   : n021.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 19:14:49 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.31  % Running portfolio for 600 s
% 0.16/0.31  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.31  % Number of cores: 8
% 0.16/0.32  % Python version: Python 3.6.8
% 0.16/0.32  % Running in FO mode
% 0.16/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.16/0.44  % Solved by: fo/fo7.sh
% 0.16/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.16/0.44  % done 36 iterations in 0.018s
% 0.16/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.16/0.44  % SZS output start Refutation
% 0.16/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.16/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.16/0.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.16/0.44  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.16/0.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.16/0.44  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.16/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.16/0.44  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.16/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.16/0.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.16/0.44  thf(d3_tarski, axiom,
% 0.16/0.44    (![A:$i,B:$i]:
% 0.16/0.44     ( ( r1_tarski @ A @ B ) <=>
% 0.16/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.16/0.44  thf('0', plain,
% 0.16/0.44      (![X1 : $i, X3 : $i]:
% 0.16/0.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.16/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.16/0.44  thf(t16_yellow_6, conjecture,
% 0.16/0.44    (![A:$i]:
% 0.16/0.44     ( ( l1_orders_2 @ A ) =>
% 0.16/0.44       ( ![B:$i]:
% 0.16/0.44         ( ( m1_yellow_0 @ B @ A ) =>
% 0.16/0.44           ( ![C:$i]: ( ( m1_yellow_0 @ C @ B ) => ( m1_yellow_0 @ C @ A ) ) ) ) ) ))).
% 0.16/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.16/0.44    (~( ![A:$i]:
% 0.16/0.44        ( ( l1_orders_2 @ A ) =>
% 0.16/0.44          ( ![B:$i]:
% 0.16/0.44            ( ( m1_yellow_0 @ B @ A ) =>
% 0.16/0.44              ( ![C:$i]: ( ( m1_yellow_0 @ C @ B ) => ( m1_yellow_0 @ C @ A ) ) ) ) ) ) )),
% 0.16/0.44    inference('cnf.neg', [status(esa)], [t16_yellow_6])).
% 0.16/0.44  thf('1', plain, ((m1_yellow_0 @ sk_C_1 @ sk_B)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf(d13_yellow_0, axiom,
% 0.16/0.44    (![A:$i]:
% 0.16/0.44     ( ( l1_orders_2 @ A ) =>
% 0.16/0.44       ( ![B:$i]:
% 0.16/0.44         ( ( l1_orders_2 @ B ) =>
% 0.16/0.44           ( ( m1_yellow_0 @ B @ A ) <=>
% 0.16/0.44             ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.16/0.44               ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ))).
% 0.16/0.44  thf('2', plain,
% 0.16/0.44      (![X4 : $i, X5 : $i]:
% 0.16/0.44         (~ (l1_orders_2 @ X4)
% 0.16/0.44          | ~ (m1_yellow_0 @ X4 @ X5)
% 0.16/0.44          | (r1_tarski @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X5))
% 0.16/0.44          | ~ (l1_orders_2 @ X5))),
% 0.16/0.44      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.16/0.44  thf('3', plain,
% 0.16/0.44      ((~ (l1_orders_2 @ sk_B)
% 0.16/0.44        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))
% 0.16/0.44        | ~ (l1_orders_2 @ sk_C_1))),
% 0.16/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.16/0.44  thf('4', plain, ((m1_yellow_0 @ sk_B @ sk_A)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf(dt_m1_yellow_0, axiom,
% 0.16/0.44    (![A:$i]:
% 0.16/0.44     ( ( l1_orders_2 @ A ) =>
% 0.16/0.44       ( ![B:$i]: ( ( m1_yellow_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.16/0.44  thf('5', plain,
% 0.16/0.44      (![X6 : $i, X7 : $i]:
% 0.16/0.44         (~ (m1_yellow_0 @ X6 @ X7) | (l1_orders_2 @ X6) | ~ (l1_orders_2 @ X7))),
% 0.16/0.44      inference('cnf', [status(esa)], [dt_m1_yellow_0])).
% 0.16/0.44  thf('6', plain, ((~ (l1_orders_2 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.16/0.44      inference('sup-', [status(thm)], ['4', '5'])).
% 0.16/0.44  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf('8', plain, ((l1_orders_2 @ sk_B)),
% 0.16/0.44      inference('demod', [status(thm)], ['6', '7'])).
% 0.16/0.44  thf('9', plain, ((m1_yellow_0 @ sk_C_1 @ sk_B)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf('10', plain,
% 0.16/0.44      (![X6 : $i, X7 : $i]:
% 0.16/0.44         (~ (m1_yellow_0 @ X6 @ X7) | (l1_orders_2 @ X6) | ~ (l1_orders_2 @ X7))),
% 0.16/0.44      inference('cnf', [status(esa)], [dt_m1_yellow_0])).
% 0.16/0.44  thf('11', plain, ((~ (l1_orders_2 @ sk_B) | (l1_orders_2 @ sk_C_1))),
% 0.16/0.44      inference('sup-', [status(thm)], ['9', '10'])).
% 0.16/0.44  thf('12', plain, ((l1_orders_2 @ sk_B)),
% 0.16/0.44      inference('demod', [status(thm)], ['6', '7'])).
% 0.16/0.44  thf('13', plain, ((l1_orders_2 @ sk_C_1)),
% 0.16/0.44      inference('demod', [status(thm)], ['11', '12'])).
% 0.16/0.44  thf('14', plain,
% 0.16/0.44      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.16/0.44      inference('demod', [status(thm)], ['3', '8', '13'])).
% 0.16/0.44  thf('15', plain,
% 0.16/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.44         (~ (r2_hidden @ X0 @ X1)
% 0.16/0.44          | (r2_hidden @ X0 @ X2)
% 0.16/0.44          | ~ (r1_tarski @ X1 @ X2))),
% 0.16/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.16/0.44  thf('16', plain,
% 0.16/0.44      (![X0 : $i]:
% 0.16/0.44         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_B))
% 0.16/0.44          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.16/0.44      inference('sup-', [status(thm)], ['14', '15'])).
% 0.16/0.44  thf('17', plain,
% 0.16/0.44      (![X0 : $i]:
% 0.16/0.44         ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ X0)
% 0.16/0.44          | (r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_C_1)) @ 
% 0.16/0.44             (u1_struct_0 @ sk_B)))),
% 0.16/0.44      inference('sup-', [status(thm)], ['0', '16'])).
% 0.16/0.44  thf('18', plain, ((m1_yellow_0 @ sk_B @ sk_A)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf('19', plain,
% 0.16/0.44      (![X4 : $i, X5 : $i]:
% 0.16/0.44         (~ (l1_orders_2 @ X4)
% 0.16/0.44          | ~ (m1_yellow_0 @ X4 @ X5)
% 0.16/0.44          | (r1_tarski @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X5))
% 0.16/0.44          | ~ (l1_orders_2 @ X5))),
% 0.16/0.44      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.16/0.44  thf('20', plain,
% 0.16/0.44      ((~ (l1_orders_2 @ sk_A)
% 0.16/0.44        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.16/0.44        | ~ (l1_orders_2 @ sk_B))),
% 0.16/0.44      inference('sup-', [status(thm)], ['18', '19'])).
% 0.16/0.44  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf('22', plain, ((l1_orders_2 @ sk_B)),
% 0.16/0.44      inference('demod', [status(thm)], ['6', '7'])).
% 0.16/0.44  thf('23', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.16/0.44      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.16/0.44  thf('24', plain,
% 0.16/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.44         (~ (r2_hidden @ X0 @ X1)
% 0.16/0.44          | (r2_hidden @ X0 @ X2)
% 0.16/0.44          | ~ (r1_tarski @ X1 @ X2))),
% 0.16/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.16/0.44  thf('25', plain,
% 0.16/0.44      (![X0 : $i]:
% 0.16/0.44         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.16/0.44          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.16/0.44      inference('sup-', [status(thm)], ['23', '24'])).
% 0.16/0.44  thf('26', plain,
% 0.16/0.44      (![X0 : $i]:
% 0.16/0.44         ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ X0)
% 0.16/0.44          | (r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_C_1)) @ 
% 0.16/0.44             (u1_struct_0 @ sk_A)))),
% 0.16/0.44      inference('sup-', [status(thm)], ['17', '25'])).
% 0.16/0.44  thf('27', plain,
% 0.16/0.44      (![X1 : $i, X3 : $i]:
% 0.16/0.44         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.16/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.16/0.44  thf('28', plain,
% 0.16/0.44      (((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.16/0.44        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.16/0.44      inference('sup-', [status(thm)], ['26', '27'])).
% 0.16/0.44  thf('29', plain,
% 0.16/0.44      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.16/0.44      inference('simplify', [status(thm)], ['28'])).
% 0.16/0.44  thf('30', plain,
% 0.16/0.44      (![X4 : $i, X5 : $i]:
% 0.16/0.44         (~ (l1_orders_2 @ X4)
% 0.16/0.44          | ~ (r1_tarski @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X5))
% 0.16/0.44          | ~ (r1_tarski @ (u1_orders_2 @ X4) @ (u1_orders_2 @ X5))
% 0.16/0.44          | (m1_yellow_0 @ X4 @ X5)
% 0.16/0.44          | ~ (l1_orders_2 @ X5))),
% 0.16/0.44      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.16/0.44  thf('31', plain,
% 0.16/0.44      ((~ (l1_orders_2 @ sk_A)
% 0.16/0.44        | (m1_yellow_0 @ sk_C_1 @ sk_A)
% 0.16/0.44        | ~ (r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_A))
% 0.16/0.44        | ~ (l1_orders_2 @ sk_C_1))),
% 0.16/0.44      inference('sup-', [status(thm)], ['29', '30'])).
% 0.16/0.44  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf('33', plain, ((l1_orders_2 @ sk_C_1)),
% 0.16/0.44      inference('demod', [status(thm)], ['11', '12'])).
% 0.16/0.44  thf('34', plain,
% 0.16/0.44      (((m1_yellow_0 @ sk_C_1 @ sk_A)
% 0.16/0.44        | ~ (r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 0.16/0.44      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.16/0.44  thf('35', plain, (~ (m1_yellow_0 @ sk_C_1 @ sk_A)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf('36', plain,
% 0.16/0.44      (~ (r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.16/0.44      inference('clc', [status(thm)], ['34', '35'])).
% 0.16/0.44  thf('37', plain,
% 0.16/0.44      (![X1 : $i, X3 : $i]:
% 0.16/0.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.16/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.16/0.44  thf('38', plain, ((m1_yellow_0 @ sk_C_1 @ sk_B)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf('39', plain,
% 0.16/0.44      (![X4 : $i, X5 : $i]:
% 0.16/0.44         (~ (l1_orders_2 @ X4)
% 0.16/0.44          | ~ (m1_yellow_0 @ X4 @ X5)
% 0.16/0.44          | (r1_tarski @ (u1_orders_2 @ X4) @ (u1_orders_2 @ X5))
% 0.16/0.44          | ~ (l1_orders_2 @ X5))),
% 0.16/0.44      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.16/0.44  thf('40', plain,
% 0.16/0.44      ((~ (l1_orders_2 @ sk_B)
% 0.16/0.44        | (r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_B))
% 0.16/0.44        | ~ (l1_orders_2 @ sk_C_1))),
% 0.16/0.44      inference('sup-', [status(thm)], ['38', '39'])).
% 0.16/0.44  thf('41', plain, ((l1_orders_2 @ sk_B)),
% 0.16/0.44      inference('demod', [status(thm)], ['6', '7'])).
% 0.16/0.44  thf('42', plain, ((l1_orders_2 @ sk_C_1)),
% 0.16/0.44      inference('demod', [status(thm)], ['11', '12'])).
% 0.16/0.44  thf('43', plain,
% 0.16/0.44      ((r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_B))),
% 0.16/0.44      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.16/0.44  thf('44', plain,
% 0.16/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.44         (~ (r2_hidden @ X0 @ X1)
% 0.16/0.44          | (r2_hidden @ X0 @ X2)
% 0.16/0.44          | ~ (r1_tarski @ X1 @ X2))),
% 0.16/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.16/0.44  thf('45', plain,
% 0.16/0.44      (![X0 : $i]:
% 0.16/0.44         ((r2_hidden @ X0 @ (u1_orders_2 @ sk_B))
% 0.16/0.44          | ~ (r2_hidden @ X0 @ (u1_orders_2 @ sk_C_1)))),
% 0.16/0.44      inference('sup-', [status(thm)], ['43', '44'])).
% 0.16/0.44  thf('46', plain,
% 0.16/0.44      (![X0 : $i]:
% 0.16/0.44         ((r1_tarski @ (u1_orders_2 @ sk_C_1) @ X0)
% 0.16/0.44          | (r2_hidden @ (sk_C @ X0 @ (u1_orders_2 @ sk_C_1)) @ 
% 0.16/0.44             (u1_orders_2 @ sk_B)))),
% 0.16/0.44      inference('sup-', [status(thm)], ['37', '45'])).
% 0.16/0.44  thf('47', plain, ((m1_yellow_0 @ sk_B @ sk_A)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf('48', plain,
% 0.16/0.44      (![X4 : $i, X5 : $i]:
% 0.16/0.44         (~ (l1_orders_2 @ X4)
% 0.16/0.44          | ~ (m1_yellow_0 @ X4 @ X5)
% 0.16/0.44          | (r1_tarski @ (u1_orders_2 @ X4) @ (u1_orders_2 @ X5))
% 0.16/0.44          | ~ (l1_orders_2 @ X5))),
% 0.16/0.44      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.16/0.44  thf('49', plain,
% 0.16/0.44      ((~ (l1_orders_2 @ sk_A)
% 0.16/0.44        | (r1_tarski @ (u1_orders_2 @ sk_B) @ (u1_orders_2 @ sk_A))
% 0.16/0.44        | ~ (l1_orders_2 @ sk_B))),
% 0.16/0.44      inference('sup-', [status(thm)], ['47', '48'])).
% 0.16/0.44  thf('50', plain, ((l1_orders_2 @ sk_A)),
% 0.16/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.44  thf('51', plain, ((l1_orders_2 @ sk_B)),
% 0.16/0.44      inference('demod', [status(thm)], ['6', '7'])).
% 0.16/0.44  thf('52', plain, ((r1_tarski @ (u1_orders_2 @ sk_B) @ (u1_orders_2 @ sk_A))),
% 0.16/0.44      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.16/0.44  thf('53', plain,
% 0.16/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.44         (~ (r2_hidden @ X0 @ X1)
% 0.16/0.44          | (r2_hidden @ X0 @ X2)
% 0.16/0.44          | ~ (r1_tarski @ X1 @ X2))),
% 0.16/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.16/0.44  thf('54', plain,
% 0.16/0.44      (![X0 : $i]:
% 0.16/0.44         ((r2_hidden @ X0 @ (u1_orders_2 @ sk_A))
% 0.16/0.44          | ~ (r2_hidden @ X0 @ (u1_orders_2 @ sk_B)))),
% 0.16/0.44      inference('sup-', [status(thm)], ['52', '53'])).
% 0.16/0.44  thf('55', plain,
% 0.16/0.44      (![X0 : $i]:
% 0.16/0.44         ((r1_tarski @ (u1_orders_2 @ sk_C_1) @ X0)
% 0.16/0.44          | (r2_hidden @ (sk_C @ X0 @ (u1_orders_2 @ sk_C_1)) @ 
% 0.16/0.44             (u1_orders_2 @ sk_A)))),
% 0.16/0.44      inference('sup-', [status(thm)], ['46', '54'])).
% 0.16/0.44  thf('56', plain,
% 0.16/0.44      (![X1 : $i, X3 : $i]:
% 0.16/0.44         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.16/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.16/0.44  thf('57', plain,
% 0.16/0.44      (((r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_A))
% 0.16/0.44        | (r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 0.16/0.44      inference('sup-', [status(thm)], ['55', '56'])).
% 0.16/0.44  thf('58', plain,
% 0.16/0.44      ((r1_tarski @ (u1_orders_2 @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.16/0.44      inference('simplify', [status(thm)], ['57'])).
% 0.16/0.44  thf('59', plain, ($false), inference('demod', [status(thm)], ['36', '58'])).
% 0.16/0.44  
% 0.16/0.44  % SZS output end Refutation
% 0.16/0.44  
% 0.16/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
