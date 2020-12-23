%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cBwTmo8b0j

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:58 EST 2020

% Result     : Theorem 37.34s
% Output     : Refutation 37.34s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 168 expanded)
%              Number of leaves         :   10 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  613 (1936 expanded)
%              Number of equality atoms :   35 ( 151 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t32_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ B )
          = ( k4_xboole_0 @ B @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_xboole_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ sk_A )
    | ( sk_A = sk_B ) ),
    inference(demod,[status(thm)],['9','10','25'])).

thf('27',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ ( sk_D @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','23'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( sk_D @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ ( sk_D @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_hidden @ ( sk_D @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','23'])).

thf('48',plain,(
    $false ),
    inference('sup-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cBwTmo8b0j
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:03:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 37.34/37.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 37.34/37.55  % Solved by: fo/fo7.sh
% 37.34/37.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 37.34/37.55  % done 26705 iterations in 37.115s
% 37.34/37.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 37.34/37.55  % SZS output start Refutation
% 37.34/37.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 37.34/37.55  thf(sk_B_type, type, sk_B: $i).
% 37.34/37.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 37.34/37.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 37.34/37.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 37.34/37.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 37.34/37.55  thf(sk_A_type, type, sk_A: $i).
% 37.34/37.55  thf(t32_xboole_1, conjecture,
% 37.34/37.55    (![A:$i,B:$i]:
% 37.34/37.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 37.34/37.55       ( ( A ) = ( B ) ) ))).
% 37.34/37.55  thf(zf_stmt_0, negated_conjecture,
% 37.34/37.55    (~( ![A:$i,B:$i]:
% 37.34/37.55        ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 37.34/37.55          ( ( A ) = ( B ) ) ) )),
% 37.34/37.55    inference('cnf.neg', [status(esa)], [t32_xboole_1])).
% 37.34/37.55  thf('0', plain,
% 37.34/37.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 37.34/37.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.34/37.55  thf(d5_xboole_0, axiom,
% 37.34/37.55    (![A:$i,B:$i,C:$i]:
% 37.34/37.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 37.34/37.55       ( ![D:$i]:
% 37.34/37.55         ( ( r2_hidden @ D @ C ) <=>
% 37.34/37.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 37.34/37.55  thf('1', plain,
% 37.34/37.55      (![X5 : $i, X6 : $i, X9 : $i]:
% 37.34/37.55         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 37.34/37.55          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 37.34/37.55          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 37.34/37.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.34/37.55  thf('2', plain,
% 37.34/37.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 37.34/37.55         (~ (r2_hidden @ X4 @ X5)
% 37.34/37.55          | (r2_hidden @ X4 @ X6)
% 37.34/37.55          | (r2_hidden @ X4 @ X7)
% 37.34/37.55          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 37.34/37.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.34/37.55  thf('3', plain,
% 37.34/37.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 37.34/37.55         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 37.34/37.55          | (r2_hidden @ X4 @ X6)
% 37.34/37.55          | ~ (r2_hidden @ X4 @ X5))),
% 37.34/37.55      inference('simplify', [status(thm)], ['2'])).
% 37.34/37.55  thf('4', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 37.34/37.55         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 37.34/37.55          | ((X2) = (k4_xboole_0 @ X0 @ X1))
% 37.34/37.55          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 37.34/37.55          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X3)))),
% 37.34/37.55      inference('sup-', [status(thm)], ['1', '3'])).
% 37.34/37.55  thf('5', plain,
% 37.34/37.55      (![X5 : $i, X6 : $i, X9 : $i]:
% 37.34/37.55         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 37.34/37.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 37.34/37.55          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 37.34/37.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.34/37.55  thf('6', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.34/37.55         ((r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 37.34/37.55          | ((X2) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 37.34/37.55          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 37.34/37.55          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 37.34/37.55          | ((X2) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 37.34/37.55      inference('sup-', [status(thm)], ['4', '5'])).
% 37.34/37.55  thf('7', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.34/37.55         ((r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 37.34/37.55          | ((X2) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 37.34/37.55          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 37.34/37.55      inference('simplify', [status(thm)], ['6'])).
% 37.34/37.55  thf('8', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i]:
% 37.34/37.55         ((r2_hidden @ (sk_D @ X0 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 37.34/37.55          | ((X0) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 37.34/37.55      inference('eq_fact', [status(thm)], ['7'])).
% 37.34/37.55  thf('9', plain,
% 37.34/37.55      (((r2_hidden @ (sk_D @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ sk_A)
% 37.34/37.55        | ((sk_A) = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))))),
% 37.34/37.55      inference('sup+', [status(thm)], ['0', '8'])).
% 37.34/37.55  thf('10', plain,
% 37.34/37.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 37.34/37.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.34/37.55  thf('11', plain,
% 37.34/37.55      (![X5 : $i, X6 : $i, X9 : $i]:
% 37.34/37.55         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 37.34/37.55          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 37.34/37.55          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 37.34/37.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.34/37.55  thf('12', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i]:
% 37.34/37.55         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.34/37.55          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.34/37.55      inference('eq_fact', [status(thm)], ['11'])).
% 37.34/37.55  thf('13', plain,
% 37.34/37.55      (![X5 : $i, X6 : $i, X9 : $i]:
% 37.34/37.55         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 37.34/37.55          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 37.34/37.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 37.34/37.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 37.34/37.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.34/37.55  thf('14', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i]:
% 37.34/37.55         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 37.34/37.55          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.34/37.55          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 37.34/37.55          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.34/37.55      inference('sup-', [status(thm)], ['12', '13'])).
% 37.34/37.55  thf('15', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i]:
% 37.34/37.55         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 37.34/37.55          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.34/37.55          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.34/37.55      inference('simplify', [status(thm)], ['14'])).
% 37.34/37.55  thf('16', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i]:
% 37.34/37.55         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 37.34/37.55          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 37.34/37.55      inference('eq_fact', [status(thm)], ['11'])).
% 37.34/37.55  thf('17', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i]:
% 37.34/37.55         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 37.34/37.55          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 37.34/37.55      inference('clc', [status(thm)], ['15', '16'])).
% 37.34/37.55  thf('18', plain,
% 37.34/37.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 37.34/37.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.34/37.55  thf('19', plain,
% 37.34/37.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 37.34/37.55         (~ (r2_hidden @ X8 @ X7)
% 37.34/37.55          | (r2_hidden @ X8 @ X5)
% 37.34/37.55          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 37.34/37.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.34/37.55  thf('20', plain,
% 37.34/37.55      (![X5 : $i, X6 : $i, X8 : $i]:
% 37.34/37.55         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 37.34/37.55      inference('simplify', [status(thm)], ['19'])).
% 37.34/37.55  thf('21', plain,
% 37.34/37.55      (![X0 : $i]:
% 37.34/37.55         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 37.34/37.55          | (r2_hidden @ X0 @ sk_B))),
% 37.34/37.55      inference('sup-', [status(thm)], ['18', '20'])).
% 37.34/37.55  thf('22', plain,
% 37.34/37.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 37.34/37.55         (~ (r2_hidden @ X8 @ X7)
% 37.34/37.55          | ~ (r2_hidden @ X8 @ X6)
% 37.34/37.55          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 37.34/37.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.34/37.55  thf('23', plain,
% 37.34/37.55      (![X5 : $i, X6 : $i, X8 : $i]:
% 37.34/37.55         (~ (r2_hidden @ X8 @ X6)
% 37.34/37.55          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 37.34/37.55      inference('simplify', [status(thm)], ['22'])).
% 37.34/37.55  thf('24', plain,
% 37.34/37.55      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 37.34/37.55      inference('clc', [status(thm)], ['21', '23'])).
% 37.34/37.55  thf('25', plain,
% 37.34/37.55      (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 37.34/37.55      inference('sup-', [status(thm)], ['17', '24'])).
% 37.34/37.55  thf('26', plain,
% 37.34/37.55      (((r2_hidden @ (sk_D @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ sk_A)
% 37.34/37.55        | ((sk_A) = (sk_B)))),
% 37.34/37.55      inference('demod', [status(thm)], ['9', '10', '25'])).
% 37.34/37.55  thf('27', plain, (((sk_A) != (sk_B))),
% 37.34/37.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.34/37.55  thf('28', plain,
% 37.34/37.55      ((r2_hidden @ (sk_D @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ sk_A)),
% 37.34/37.55      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 37.34/37.55  thf(d3_tarski, axiom,
% 37.34/37.55    (![A:$i,B:$i]:
% 37.34/37.55     ( ( r1_tarski @ A @ B ) <=>
% 37.34/37.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 37.34/37.55  thf('29', plain,
% 37.34/37.55      (![X1 : $i, X3 : $i]:
% 37.34/37.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 37.34/37.55      inference('cnf', [status(esa)], [d3_tarski])).
% 37.34/37.55  thf('30', plain,
% 37.34/37.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 37.34/37.55         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 37.34/37.55          | (r2_hidden @ X4 @ X6)
% 37.34/37.55          | ~ (r2_hidden @ X4 @ X5))),
% 37.34/37.55      inference('simplify', [status(thm)], ['2'])).
% 37.34/37.55  thf('31', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.34/37.55         ((r1_tarski @ X0 @ X1)
% 37.34/37.55          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 37.34/37.55          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 37.34/37.55      inference('sup-', [status(thm)], ['29', '30'])).
% 37.34/37.55  thf('32', plain,
% 37.34/37.55      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 37.34/37.55      inference('clc', [status(thm)], ['21', '23'])).
% 37.34/37.55  thf('33', plain,
% 37.34/37.55      (![X0 : $i]:
% 37.34/37.55         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B) | (r1_tarski @ sk_A @ X0))),
% 37.34/37.55      inference('sup-', [status(thm)], ['31', '32'])).
% 37.34/37.55  thf('34', plain,
% 37.34/37.55      (![X1 : $i, X3 : $i]:
% 37.34/37.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 37.34/37.55      inference('cnf', [status(esa)], [d3_tarski])).
% 37.34/37.55  thf('35', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 37.34/37.55      inference('sup-', [status(thm)], ['33', '34'])).
% 37.34/37.55  thf('36', plain, ((r1_tarski @ sk_A @ sk_B)),
% 37.34/37.55      inference('simplify', [status(thm)], ['35'])).
% 37.34/37.55  thf('37', plain,
% 37.34/37.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.34/37.55         (~ (r2_hidden @ X0 @ X1)
% 37.34/37.55          | (r2_hidden @ X0 @ X2)
% 37.34/37.55          | ~ (r1_tarski @ X1 @ X2))),
% 37.34/37.55      inference('cnf', [status(esa)], [d3_tarski])).
% 37.34/37.55  thf('38', plain,
% 37.34/37.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 37.34/37.55      inference('sup-', [status(thm)], ['36', '37'])).
% 37.34/37.55  thf('39', plain,
% 37.34/37.55      ((r2_hidden @ (sk_D @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ sk_B)),
% 37.34/37.55      inference('sup-', [status(thm)], ['28', '38'])).
% 37.34/37.55  thf('40', plain,
% 37.34/37.55      (![X5 : $i, X6 : $i, X9 : $i]:
% 37.34/37.55         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 37.34/37.55          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 37.34/37.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 37.34/37.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 37.34/37.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 37.34/37.55  thf('41', plain,
% 37.34/37.55      ((~ (r2_hidden @ (sk_D @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ 
% 37.34/37.55           sk_A)
% 37.34/37.55        | (r2_hidden @ (sk_D @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ 
% 37.34/37.55           (k4_xboole_0 @ sk_A @ sk_B))
% 37.34/37.55        | ((sk_A) = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 37.34/37.55      inference('sup-', [status(thm)], ['39', '40'])).
% 37.34/37.55  thf('42', plain,
% 37.34/37.55      ((r2_hidden @ (sk_D @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ sk_A)),
% 37.34/37.55      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 37.34/37.55  thf('43', plain,
% 37.34/37.55      (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 37.34/37.55      inference('sup-', [status(thm)], ['17', '24'])).
% 37.34/37.55  thf('44', plain,
% 37.34/37.55      (((r2_hidden @ (sk_D @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ 
% 37.34/37.55         (k4_xboole_0 @ sk_A @ sk_B))
% 37.34/37.55        | ((sk_A) = (sk_B)))),
% 37.34/37.55      inference('demod', [status(thm)], ['41', '42', '43'])).
% 37.34/37.55  thf('45', plain, (((sk_A) != (sk_B))),
% 37.34/37.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.34/37.55  thf('46', plain,
% 37.34/37.55      ((r2_hidden @ (sk_D @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ 
% 37.34/37.55        (k4_xboole_0 @ sk_A @ sk_B))),
% 37.34/37.55      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 37.34/37.55  thf('47', plain,
% 37.34/37.55      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 37.34/37.55      inference('clc', [status(thm)], ['21', '23'])).
% 37.34/37.55  thf('48', plain, ($false), inference('sup-', [status(thm)], ['46', '47'])).
% 37.34/37.55  
% 37.34/37.55  % SZS output end Refutation
% 37.34/37.55  
% 37.34/37.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
