%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R0AcqSD1aJ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:40 EST 2020

% Result     : Theorem 19.86s
% Output     : Refutation 19.86s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 138 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  557 (1430 expanded)
%              Number of equality atoms :   48 ( 121 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['3','8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X2 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X2 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X2
        = ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ k1_xboole_0 )
    | ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','38'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['3','8'])).

thf('42',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['39','42'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference('sup-',[status(thm)],['43','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R0AcqSD1aJ
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 19.86/20.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.86/20.07  % Solved by: fo/fo7.sh
% 19.86/20.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.86/20.07  % done 17868 iterations in 19.618s
% 19.86/20.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.86/20.07  % SZS output start Refutation
% 19.86/20.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 19.86/20.07  thf(sk_B_type, type, sk_B: $i).
% 19.86/20.07  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 19.86/20.07  thf(sk_A_type, type, sk_A: $i).
% 19.86/20.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 19.86/20.07  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 19.86/20.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.86/20.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 19.86/20.07  thf(t83_xboole_1, conjecture,
% 19.86/20.07    (![A:$i,B:$i]:
% 19.86/20.07     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 19.86/20.07  thf(zf_stmt_0, negated_conjecture,
% 19.86/20.07    (~( ![A:$i,B:$i]:
% 19.86/20.07        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 19.86/20.07    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 19.86/20.07  thf('0', plain,
% 19.86/20.07      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 19.86/20.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.86/20.07  thf('1', plain,
% 19.86/20.07      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 19.86/20.07      inference('split', [status(esa)], ['0'])).
% 19.86/20.07  thf('2', plain,
% 19.86/20.07      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 19.86/20.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.86/20.07  thf('3', plain,
% 19.86/20.07      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 19.86/20.07       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 19.86/20.07      inference('split', [status(esa)], ['2'])).
% 19.86/20.07  thf('4', plain,
% 19.86/20.07      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 19.86/20.07         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 19.86/20.07      inference('split', [status(esa)], ['0'])).
% 19.86/20.07  thf(t79_xboole_1, axiom,
% 19.86/20.07    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 19.86/20.07  thf('5', plain,
% 19.86/20.07      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 19.86/20.07      inference('cnf', [status(esa)], [t79_xboole_1])).
% 19.86/20.07  thf('6', plain,
% 19.86/20.07      (((r1_xboole_0 @ sk_A @ sk_B))
% 19.86/20.07         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 19.86/20.07      inference('sup+', [status(thm)], ['4', '5'])).
% 19.86/20.07  thf('7', plain,
% 19.86/20.07      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 19.86/20.07      inference('split', [status(esa)], ['2'])).
% 19.86/20.07  thf('8', plain,
% 19.86/20.07      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 19.86/20.07       ~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 19.86/20.07      inference('sup-', [status(thm)], ['6', '7'])).
% 19.86/20.07  thf('9', plain,
% 19.86/20.07      (((r1_xboole_0 @ sk_A @ sk_B)) | (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 19.86/20.07      inference('split', [status(esa)], ['0'])).
% 19.86/20.07  thf('10', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 19.86/20.07      inference('sat_resolution*', [status(thm)], ['3', '8', '9'])).
% 19.86/20.07  thf('11', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 19.86/20.07      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 19.86/20.07  thf(d7_xboole_0, axiom,
% 19.86/20.07    (![A:$i,B:$i]:
% 19.86/20.07     ( ( r1_xboole_0 @ A @ B ) <=>
% 19.86/20.07       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 19.86/20.07  thf('12', plain,
% 19.86/20.07      (![X6 : $i, X7 : $i]:
% 19.86/20.07         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 19.86/20.07      inference('cnf', [status(esa)], [d7_xboole_0])).
% 19.86/20.07  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 19.86/20.07      inference('sup-', [status(thm)], ['11', '12'])).
% 19.86/20.07  thf(t48_xboole_1, axiom,
% 19.86/20.07    (![A:$i,B:$i]:
% 19.86/20.07     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 19.86/20.07  thf('14', plain,
% 19.86/20.07      (![X10 : $i, X11 : $i]:
% 19.86/20.07         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 19.86/20.07           = (k3_xboole_0 @ X10 @ X11))),
% 19.86/20.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.86/20.07  thf(d5_xboole_0, axiom,
% 19.86/20.07    (![A:$i,B:$i,C:$i]:
% 19.86/20.07     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 19.86/20.07       ( ![D:$i]:
% 19.86/20.07         ( ( r2_hidden @ D @ C ) <=>
% 19.86/20.07           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 19.86/20.07  thf('15', plain,
% 19.86/20.07      (![X1 : $i, X2 : $i, X5 : $i]:
% 19.86/20.07         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 19.86/20.07          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 19.86/20.07          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 19.86/20.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 19.86/20.07  thf('16', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.86/20.07          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.86/20.07      inference('eq_fact', [status(thm)], ['15'])).
% 19.86/20.07  thf('17', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.86/20.07         (~ (r2_hidden @ X0 @ X1)
% 19.86/20.07          | (r2_hidden @ X0 @ X2)
% 19.86/20.07          | (r2_hidden @ X0 @ X3)
% 19.86/20.07          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 19.86/20.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 19.86/20.07  thf('18', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.86/20.07         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 19.86/20.07          | (r2_hidden @ X0 @ X2)
% 19.86/20.07          | ~ (r2_hidden @ X0 @ X1))),
% 19.86/20.07      inference('simplify', [status(thm)], ['17'])).
% 19.86/20.07  thf('19', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.86/20.07         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 19.86/20.07          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2)
% 19.86/20.07          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 19.86/20.07      inference('sup-', [status(thm)], ['16', '18'])).
% 19.86/20.07  thf('20', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.86/20.07         ((r2_hidden @ (sk_D @ X1 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 19.86/20.07          | (r2_hidden @ (sk_D @ X1 @ X2 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 19.86/20.07          | ((X1) = (k4_xboole_0 @ X1 @ X2)))),
% 19.86/20.07      inference('sup+', [status(thm)], ['14', '19'])).
% 19.86/20.07  thf('21', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.86/20.07          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.86/20.07      inference('eq_fact', [status(thm)], ['15'])).
% 19.86/20.07  thf('22', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.86/20.07          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.86/20.07      inference('eq_fact', [status(thm)], ['15'])).
% 19.86/20.07  thf('23', plain,
% 19.86/20.07      (![X1 : $i, X2 : $i, X5 : $i]:
% 19.86/20.07         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 19.86/20.07          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 19.86/20.07          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 19.86/20.07          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 19.86/20.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 19.86/20.07  thf('24', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 19.86/20.07          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.86/20.07          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 19.86/20.07          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.86/20.07      inference('sup-', [status(thm)], ['22', '23'])).
% 19.86/20.07  thf('25', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 19.86/20.07          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.86/20.07          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.86/20.07      inference('simplify', [status(thm)], ['24'])).
% 19.86/20.07  thf('26', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.86/20.07          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.86/20.07      inference('eq_fact', [status(thm)], ['15'])).
% 19.86/20.07  thf('27', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 19.86/20.07          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 19.86/20.07      inference('clc', [status(thm)], ['25', '26'])).
% 19.86/20.07  thf('28', plain,
% 19.86/20.07      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 19.86/20.07         (~ (r2_hidden @ X4 @ X3)
% 19.86/20.07          | ~ (r2_hidden @ X4 @ X2)
% 19.86/20.07          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 19.86/20.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 19.86/20.07  thf('29', plain,
% 19.86/20.07      (![X1 : $i, X2 : $i, X4 : $i]:
% 19.86/20.07         (~ (r2_hidden @ X4 @ X2)
% 19.86/20.07          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 19.86/20.07      inference('simplify', [status(thm)], ['28'])).
% 19.86/20.07  thf('30', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.86/20.07         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 19.86/20.07          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 19.86/20.07      inference('sup-', [status(thm)], ['27', '29'])).
% 19.86/20.07  thf('31', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 19.86/20.07          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 19.86/20.07      inference('sup-', [status(thm)], ['21', '30'])).
% 19.86/20.07  thf('32', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.86/20.07      inference('simplify', [status(thm)], ['31'])).
% 19.86/20.07  thf('33', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.86/20.07         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 19.86/20.07          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 19.86/20.07      inference('sup-', [status(thm)], ['27', '29'])).
% 19.86/20.07  thf('34', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.86/20.07         (~ (r2_hidden @ (sk_D @ X2 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0))
% 19.86/20.07          | ((X2)
% 19.86/20.07              = (k4_xboole_0 @ X2 @ 
% 19.86/20.07                 (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))))),
% 19.86/20.07      inference('sup-', [status(thm)], ['32', '33'])).
% 19.86/20.07  thf('35', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.86/20.07      inference('simplify', [status(thm)], ['31'])).
% 19.86/20.07  thf('36', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.86/20.07         (~ (r2_hidden @ (sk_D @ X2 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0))
% 19.86/20.07          | ((X2) = (k4_xboole_0 @ X2 @ X0)))),
% 19.86/20.07      inference('demod', [status(thm)], ['34', '35'])).
% 19.86/20.07  thf('37', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         (((X1) = (k4_xboole_0 @ X1 @ X0))
% 19.86/20.07          | (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 19.86/20.07          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 19.86/20.07      inference('sup-', [status(thm)], ['20', '36'])).
% 19.86/20.07  thf('38', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         ((r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 19.86/20.07          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 19.86/20.07      inference('simplify', [status(thm)], ['37'])).
% 19.86/20.07  thf('39', plain,
% 19.86/20.07      (((r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ k1_xboole_0)
% 19.86/20.07        | ((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))),
% 19.86/20.07      inference('sup+', [status(thm)], ['13', '38'])).
% 19.86/20.07  thf('40', plain,
% 19.86/20.07      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 19.86/20.07         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 19.86/20.07      inference('split', [status(esa)], ['2'])).
% 19.86/20.07  thf('41', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 19.86/20.07      inference('sat_resolution*', [status(thm)], ['3', '8'])).
% 19.86/20.07  thf('42', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 19.86/20.07      inference('simpl_trail', [status(thm)], ['40', '41'])).
% 19.86/20.07  thf('43', plain, ((r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ k1_xboole_0)),
% 19.86/20.07      inference('simplify_reflect-', [status(thm)], ['39', '42'])).
% 19.86/20.07  thf(t3_boole, axiom,
% 19.86/20.07    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 19.86/20.07  thf('44', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 19.86/20.07      inference('cnf', [status(esa)], [t3_boole])).
% 19.86/20.07  thf('45', plain,
% 19.86/20.07      (![X1 : $i, X2 : $i, X4 : $i]:
% 19.86/20.07         (~ (r2_hidden @ X4 @ X2)
% 19.86/20.07          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 19.86/20.07      inference('simplify', [status(thm)], ['28'])).
% 19.86/20.07  thf('46', plain,
% 19.86/20.07      (![X0 : $i, X1 : $i]:
% 19.86/20.07         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 19.86/20.07      inference('sup-', [status(thm)], ['44', '45'])).
% 19.86/20.07  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 19.86/20.07      inference('condensation', [status(thm)], ['46'])).
% 19.86/20.07  thf('48', plain, ($false), inference('sup-', [status(thm)], ['43', '47'])).
% 19.86/20.07  
% 19.86/20.07  % SZS output end Refutation
% 19.86/20.07  
% 19.86/20.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
