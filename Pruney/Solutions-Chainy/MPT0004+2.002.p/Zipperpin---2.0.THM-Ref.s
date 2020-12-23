%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eQRWsIwrz8

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 159 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  411 (1750 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t4_xboole_0,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( ? [C: $i] :
                ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
            & ( r1_xboole_0 @ A @ B ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ B )
            & ! [C: $i] :
                ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_xboole_0])).

thf('0',plain,(
    ! [X10: $i] :
      ( ( r1_xboole_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X10: $i] :
      ( ( r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ! [X10: $i] :
        ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ! [X10: $i] :
        ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ! [X10: $i] :
        ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ! [X10: $i] :
          ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('16',plain,
    ( ! [X10: $i] :
        ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ! [X10: $i] :
        ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('17',plain,
    ( ~ ! [X10: $i] :
          ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('19',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ! [X10: $i] :
        ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['14','17','18','19'])).

thf('21',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('30',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ! [X10: $i] :
        ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('31',plain,(
    r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['14','17','18','30'])).

thf('32',plain,(
    r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('34',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    r2_hidden @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['38','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eQRWsIwrz8
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:48:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 58 iterations in 0.029s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(t4_xboole_0, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47               ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47          ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.47               ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t4_xboole_0])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X10 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ sk_A @ sk_B)
% 0.20/0.47          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf(t3_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.47            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.47  thf(d4_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.47       ( ![D:$i]:
% 0.20/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.47           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.47          | ~ (r2_hidden @ X0 @ X2)
% 0.20/0.47          | (r2_hidden @ X0 @ X3)
% 0.20/0.47          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ X2)
% 0.20/0.47          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.47          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2)
% 0.20/0.47          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.47          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.20/0.47          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.20/0.47          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X10 : $i]:
% 0.20/0.47         ((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.20/0.47          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.47         <= ((![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.20/0.47         <= ((![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.20/0.47       ~ (![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.47         <= (((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['12'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.47         <= ((![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['9'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (~ (![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B))) | 
% 0.20/0.47       ~ ((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))) | 
% 0.20/0.47       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.47      inference('split', [status(esa)], ['12'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.20/0.47       (![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('20', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['14', '17', '18', '19'])).
% 0.20/0.47  thf('21', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.47          | ~ (r2_hidden @ X8 @ X9)
% 0.20/0.47          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.47          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.47          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.47          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.20/0.47          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.47  thf('28', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.47         <= (((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['12'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))) | 
% 0.20/0.47       (![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['9'])).
% 0.20/0.47  thf('31', plain, (((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['14', '17', '18', '30'])).
% 0.20/0.47  thf('32', plain, ((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['29', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.47          | (r2_hidden @ X4 @ X2)
% 0.20/0.47          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.47         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.47  thf('35', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['32', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.47          | ~ (r2_hidden @ X8 @ X9)
% 0.20/0.47          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | ~ (r2_hidden @ sk_C_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain, (~ (r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['28', '37'])).
% 0.20/0.47  thf('39', plain, ((r2_hidden @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['29', '31'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.47          | (r2_hidden @ X4 @ X1)
% 0.20/0.47          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.47         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.47  thf('42', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['39', '41'])).
% 0.20/0.47  thf('43', plain, ($false), inference('demod', [status(thm)], ['38', '42'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
