%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iu0VebXReY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:41 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   46 (  92 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  387 ( 857 expanded)
%              Number of equality atoms :   33 (  72 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t83_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ A @ B )
      <=> ( ( k4_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t83_xboole_1])).

thf('0',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

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

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_A @ X0 )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,
    ( ( ( r1_xboole_0 @ sk_A @ sk_B )
      | ( r1_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['3','14','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('26',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['3','14'])).

thf('33',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iu0VebXReY
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.67/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.86  % Solved by: fo/fo7.sh
% 0.67/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.86  % done 470 iterations in 0.410s
% 0.67/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.86  % SZS output start Refutation
% 0.67/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.86  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.67/0.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.86  thf(t83_xboole_1, conjecture,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.67/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.86    (~( ![A:$i,B:$i]:
% 0.67/0.86        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.67/0.86    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 0.67/0.86  thf('0', plain,
% 0.67/0.86      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('1', plain,
% 0.67/0.86      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.67/0.86      inference('split', [status(esa)], ['0'])).
% 0.67/0.86  thf('2', plain,
% 0.67/0.86      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('3', plain,
% 0.67/0.86      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 0.67/0.86       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.86      inference('split', [status(esa)], ['2'])).
% 0.67/0.86  thf(t3_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.67/0.86            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.86       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.67/0.86            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.67/0.86  thf('4', plain,
% 0.67/0.86      (![X6 : $i, X7 : $i]:
% 0.67/0.86         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.86  thf('5', plain,
% 0.67/0.86      (![X6 : $i, X7 : $i]:
% 0.67/0.86         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.86  thf('6', plain,
% 0.67/0.86      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.67/0.86         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.67/0.86      inference('split', [status(esa)], ['0'])).
% 0.67/0.86  thf(d5_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.67/0.86       ( ![D:$i]:
% 0.67/0.86         ( ( r2_hidden @ D @ C ) <=>
% 0.67/0.86           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.67/0.86  thf('7', plain,
% 0.67/0.86      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X4 @ X3)
% 0.67/0.86          | ~ (r2_hidden @ X4 @ X2)
% 0.67/0.86          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.67/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.67/0.86  thf('8', plain,
% 0.67/0.86      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X4 @ X2)
% 0.67/0.86          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['7'])).
% 0.67/0.86  thf('9', plain,
% 0.67/0.86      ((![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.67/0.86         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['6', '8'])).
% 0.67/0.86  thf('10', plain,
% 0.67/0.86      ((![X0 : $i]:
% 0.67/0.86          ((r1_xboole_0 @ sk_A @ X0)
% 0.67/0.86           | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)))
% 0.67/0.86         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['5', '9'])).
% 0.67/0.86  thf('11', plain,
% 0.67/0.86      ((((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_A @ sk_B)))
% 0.67/0.86         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['4', '10'])).
% 0.67/0.86  thf('12', plain,
% 0.67/0.86      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.67/0.86         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.67/0.86      inference('simplify', [status(thm)], ['11'])).
% 0.67/0.86  thf('13', plain,
% 0.67/0.86      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.67/0.86      inference('split', [status(esa)], ['2'])).
% 0.67/0.86  thf('14', plain,
% 0.67/0.86      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.67/0.86       ~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['12', '13'])).
% 0.67/0.86  thf('15', plain,
% 0.67/0.86      (((r1_xboole_0 @ sk_A @ sk_B)) | (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.67/0.86      inference('split', [status(esa)], ['0'])).
% 0.67/0.86  thf('16', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.86      inference('sat_resolution*', [status(thm)], ['3', '14', '15'])).
% 0.67/0.86  thf('17', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.67/0.86      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.67/0.86  thf('18', plain,
% 0.67/0.86      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.67/0.86         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.67/0.86          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.67/0.86          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.67/0.86  thf('19', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.67/0.86          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.67/0.86      inference('eq_fact', [status(thm)], ['18'])).
% 0.67/0.86  thf('20', plain,
% 0.67/0.86      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.67/0.86         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.67/0.86          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.67/0.86          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.67/0.86          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.67/0.86  thf('21', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.67/0.86          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.67/0.86          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.67/0.86          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['19', '20'])).
% 0.67/0.86  thf('22', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.67/0.86          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.67/0.86          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['21'])).
% 0.67/0.86  thf('23', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.67/0.86          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.67/0.86      inference('eq_fact', [status(thm)], ['18'])).
% 0.67/0.86  thf('24', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.67/0.86          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.67/0.86      inference('clc', [status(thm)], ['22', '23'])).
% 0.67/0.86  thf('25', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.67/0.86          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.67/0.86      inference('eq_fact', [status(thm)], ['18'])).
% 0.67/0.86  thf('26', plain,
% 0.67/0.86      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X8 @ X6)
% 0.67/0.86          | ~ (r2_hidden @ X8 @ X9)
% 0.67/0.86          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.86  thf('27', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.86         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.67/0.86          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.67/0.86          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2))),
% 0.67/0.86      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.86  thf('28', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (((X1) = (k4_xboole_0 @ X1 @ X0))
% 0.67/0.86          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.67/0.86          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['24', '27'])).
% 0.67/0.86  thf('29', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (r1_xboole_0 @ X1 @ X0) | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['28'])).
% 0.67/0.86  thf('30', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['17', '29'])).
% 0.67/0.86  thf('31', plain,
% 0.67/0.86      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 0.67/0.86         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.67/0.86      inference('split', [status(esa)], ['2'])).
% 0.67/0.86  thf('32', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.67/0.86      inference('sat_resolution*', [status(thm)], ['3', '14'])).
% 0.67/0.86  thf('33', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.67/0.86      inference('simpl_trail', [status(thm)], ['31', '32'])).
% 0.67/0.86  thf('34', plain, ($false),
% 0.67/0.86      inference('simplify_reflect-', [status(thm)], ['30', '33'])).
% 0.67/0.86  
% 0.67/0.86  % SZS output end Refutation
% 0.67/0.86  
% 0.71/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
