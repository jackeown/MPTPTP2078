%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b5ykjW1la7

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:10 EST 2020

% Result     : Theorem 6.56s
% Output     : Refutation 6.56s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 308 expanded)
%              Number of leaves         :   15 (  90 expanded)
%              Depth                    :   21
%              Number of atoms          :  554 (3328 expanded)
%              Number of equality atoms :   33 ( 197 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X16 ) )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t115_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ A )
        = ( k2_zfmisc_1 @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ A )
          = ( k2_zfmisc_1 @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t115_zfmisc_1])).

thf('7',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_A )
    = ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(condensation,[status(thm)],['10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X11 ) @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X16 ) )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ sk_B ) @ ( sk_C_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_A )
    = ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ sk_B ) @ ( sk_C_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X11 ) @ X10 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('45',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('47',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b5ykjW1la7
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:59:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 6.56/6.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.56/6.76  % Solved by: fo/fo7.sh
% 6.56/6.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.56/6.76  % done 3554 iterations in 6.309s
% 6.56/6.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.56/6.76  % SZS output start Refutation
% 6.56/6.76  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.56/6.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.56/6.76  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.56/6.76  thf(sk_A_type, type, sk_A: $i).
% 6.56/6.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.56/6.76  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.56/6.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.56/6.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.56/6.76  thf(sk_B_type, type, sk_B: $i).
% 6.56/6.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.56/6.76  thf(d4_xboole_0, axiom,
% 6.56/6.76    (![A:$i,B:$i,C:$i]:
% 6.56/6.76     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 6.56/6.76       ( ![D:$i]:
% 6.56/6.76         ( ( r2_hidden @ D @ C ) <=>
% 6.56/6.76           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 6.56/6.76  thf('0', plain,
% 6.56/6.76      (![X5 : $i, X6 : $i, X9 : $i]:
% 6.56/6.76         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 6.56/6.76          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 6.56/6.76          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 6.56/6.76      inference('cnf', [status(esa)], [d4_xboole_0])).
% 6.56/6.76  thf('1', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i]:
% 6.56/6.76         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 6.56/6.76          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 6.56/6.76      inference('eq_fact', [status(thm)], ['0'])).
% 6.56/6.76  thf(d3_tarski, axiom,
% 6.56/6.76    (![A:$i,B:$i]:
% 6.56/6.76     ( ( r1_tarski @ A @ B ) <=>
% 6.56/6.76       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.56/6.76  thf('2', plain,
% 6.56/6.76      (![X1 : $i, X3 : $i]:
% 6.56/6.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.56/6.76      inference('cnf', [status(esa)], [d3_tarski])).
% 6.56/6.76  thf('3', plain,
% 6.56/6.76      (![X1 : $i, X3 : $i]:
% 6.56/6.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.56/6.76      inference('cnf', [status(esa)], [d3_tarski])).
% 6.56/6.76  thf(l54_zfmisc_1, axiom,
% 6.56/6.76    (![A:$i,B:$i,C:$i,D:$i]:
% 6.56/6.76     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 6.56/6.76       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 6.56/6.76  thf('4', plain,
% 6.56/6.76      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 6.56/6.76         ((r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X16))
% 6.56/6.76          | ~ (r2_hidden @ X14 @ X16)
% 6.56/6.76          | ~ (r2_hidden @ X12 @ X13))),
% 6.56/6.76      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.56/6.76  thf('5', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.56/6.76         ((r1_tarski @ X0 @ X1)
% 6.56/6.76          | ~ (r2_hidden @ X3 @ X2)
% 6.56/6.76          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 6.56/6.76             (k2_zfmisc_1 @ X2 @ X0)))),
% 6.56/6.76      inference('sup-', [status(thm)], ['3', '4'])).
% 6.56/6.76  thf('6', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.56/6.76         ((r1_tarski @ X0 @ X1)
% 6.56/6.76          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 6.56/6.76             (k2_zfmisc_1 @ X0 @ X2))
% 6.56/6.76          | (r1_tarski @ X2 @ X3))),
% 6.56/6.76      inference('sup-', [status(thm)], ['2', '5'])).
% 6.56/6.76  thf(t115_zfmisc_1, conjecture,
% 6.56/6.76    (![A:$i,B:$i]:
% 6.56/6.76     ( ( ( k2_zfmisc_1 @ A @ A ) = ( k2_zfmisc_1 @ B @ B ) ) =>
% 6.56/6.76       ( ( A ) = ( B ) ) ))).
% 6.56/6.76  thf(zf_stmt_0, negated_conjecture,
% 6.56/6.76    (~( ![A:$i,B:$i]:
% 6.56/6.76        ( ( ( k2_zfmisc_1 @ A @ A ) = ( k2_zfmisc_1 @ B @ B ) ) =>
% 6.56/6.76          ( ( A ) = ( B ) ) ) )),
% 6.56/6.76    inference('cnf.neg', [status(esa)], [t115_zfmisc_1])).
% 6.56/6.76  thf('7', plain,
% 6.56/6.76      (((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_zfmisc_1 @ sk_B @ sk_B))),
% 6.56/6.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.56/6.76  thf('8', plain,
% 6.56/6.76      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 6.56/6.76         ((r2_hidden @ X12 @ X13)
% 6.56/6.76          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X15)))),
% 6.56/6.76      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.56/6.76  thf('9', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i]:
% 6.56/6.76         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 6.56/6.76          | (r2_hidden @ X1 @ sk_B))),
% 6.56/6.76      inference('sup-', [status(thm)], ['7', '8'])).
% 6.56/6.76  thf('10', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i]:
% 6.56/6.76         ((r1_tarski @ sk_A @ X0)
% 6.56/6.76          | (r1_tarski @ sk_A @ X1)
% 6.56/6.76          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B))),
% 6.56/6.76      inference('sup-', [status(thm)], ['6', '9'])).
% 6.56/6.76  thf('11', plain,
% 6.56/6.76      (![X0 : $i]:
% 6.56/6.76         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B) | (r1_tarski @ sk_A @ X0))),
% 6.56/6.76      inference('condensation', [status(thm)], ['10'])).
% 6.56/6.76  thf('12', plain,
% 6.56/6.76      (![X1 : $i, X3 : $i]:
% 6.56/6.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 6.56/6.76      inference('cnf', [status(esa)], [d3_tarski])).
% 6.56/6.76  thf('13', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 6.56/6.76      inference('sup-', [status(thm)], ['11', '12'])).
% 6.56/6.76  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 6.56/6.76      inference('simplify', [status(thm)], ['13'])).
% 6.56/6.76  thf('15', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.56/6.76         (~ (r2_hidden @ X0 @ X1)
% 6.56/6.76          | (r2_hidden @ X0 @ X2)
% 6.56/6.76          | ~ (r1_tarski @ X1 @ X2))),
% 6.56/6.76      inference('cnf', [status(esa)], [d3_tarski])).
% 6.56/6.76  thf('16', plain,
% 6.56/6.76      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 6.56/6.76      inference('sup-', [status(thm)], ['14', '15'])).
% 6.56/6.76  thf('17', plain,
% 6.56/6.76      (![X0 : $i]:
% 6.56/6.76         (((sk_A) = (k3_xboole_0 @ X0 @ sk_A))
% 6.56/6.76          | (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ sk_B))),
% 6.56/6.76      inference('sup-', [status(thm)], ['1', '16'])).
% 6.56/6.76  thf('18', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i]:
% 6.56/6.76         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 6.56/6.76          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 6.56/6.76      inference('eq_fact', [status(thm)], ['0'])).
% 6.56/6.76  thf('19', plain,
% 6.56/6.76      (![X5 : $i, X6 : $i, X9 : $i]:
% 6.56/6.76         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 6.56/6.76          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 6.56/6.76          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 6.56/6.76          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 6.56/6.76      inference('cnf', [status(esa)], [d4_xboole_0])).
% 6.56/6.76  thf('20', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i]:
% 6.56/6.76         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 6.56/6.76          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 6.56/6.76          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 6.56/6.76          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 6.56/6.76      inference('sup-', [status(thm)], ['18', '19'])).
% 6.56/6.76  thf('21', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i]:
% 6.56/6.76         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 6.56/6.76          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 6.56/6.76          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 6.56/6.76      inference('simplify', [status(thm)], ['20'])).
% 6.56/6.76  thf('22', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i]:
% 6.56/6.76         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 6.56/6.76          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 6.56/6.76      inference('eq_fact', [status(thm)], ['0'])).
% 6.56/6.76  thf('23', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i]:
% 6.56/6.76         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 6.56/6.76          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 6.56/6.76      inference('clc', [status(thm)], ['21', '22'])).
% 6.56/6.76  thf('24', plain,
% 6.56/6.76      ((((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 6.56/6.76        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 6.56/6.76      inference('sup-', [status(thm)], ['17', '23'])).
% 6.56/6.76  thf('25', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 6.56/6.76      inference('simplify', [status(thm)], ['24'])).
% 6.56/6.76  thf(t2_tarski, axiom,
% 6.56/6.76    (![A:$i,B:$i]:
% 6.56/6.76     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 6.56/6.76       ( ( A ) = ( B ) ) ))).
% 6.56/6.76  thf('26', plain,
% 6.56/6.76      (![X10 : $i, X11 : $i]:
% 6.56/6.76         (((X11) = (X10))
% 6.56/6.76          | (r2_hidden @ (sk_C_1 @ X10 @ X11) @ X10)
% 6.56/6.76          | (r2_hidden @ (sk_C_1 @ X10 @ X11) @ X11))),
% 6.56/6.76      inference('cnf', [status(esa)], [t2_tarski])).
% 6.56/6.76  thf('27', plain,
% 6.56/6.76      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.56/6.76         (~ (r2_hidden @ X8 @ X7)
% 6.56/6.76          | (r2_hidden @ X8 @ X5)
% 6.56/6.76          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 6.56/6.76      inference('cnf', [status(esa)], [d4_xboole_0])).
% 6.56/6.76  thf('28', plain,
% 6.56/6.76      (![X5 : $i, X6 : $i, X8 : $i]:
% 6.56/6.76         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 6.56/6.76      inference('simplify', [status(thm)], ['27'])).
% 6.56/6.76  thf('29', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.56/6.76         ((r2_hidden @ (sk_C_1 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X2)
% 6.56/6.76          | ((X2) = (k3_xboole_0 @ X1 @ X0))
% 6.56/6.76          | (r2_hidden @ (sk_C_1 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 6.56/6.76      inference('sup-', [status(thm)], ['26', '28'])).
% 6.56/6.76  thf('30', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i]:
% 6.56/6.76         ((r2_hidden @ (sk_C_1 @ (k3_xboole_0 @ X0 @ X1) @ X0) @ X0)
% 6.56/6.76          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 6.56/6.76      inference('eq_fact', [status(thm)], ['29'])).
% 6.56/6.76  thf('31', plain,
% 6.56/6.76      (((r2_hidden @ (sk_C_1 @ sk_A @ sk_B) @ sk_B)
% 6.56/6.76        | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 6.56/6.76      inference('sup+', [status(thm)], ['25', '30'])).
% 6.56/6.76  thf('32', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 6.56/6.76      inference('simplify', [status(thm)], ['24'])).
% 6.56/6.76  thf('33', plain,
% 6.56/6.76      (((r2_hidden @ (sk_C_1 @ sk_A @ sk_B) @ sk_B) | ((sk_B) = (sk_A)))),
% 6.56/6.76      inference('demod', [status(thm)], ['31', '32'])).
% 6.56/6.76  thf('34', plain, (((sk_A) != (sk_B))),
% 6.56/6.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.56/6.76  thf('35', plain, ((r2_hidden @ (sk_C_1 @ sk_A @ sk_B) @ sk_B)),
% 6.56/6.76      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 6.56/6.76  thf('36', plain, ((r2_hidden @ (sk_C_1 @ sk_A @ sk_B) @ sk_B)),
% 6.56/6.76      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 6.56/6.76  thf('37', plain,
% 6.56/6.76      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 6.56/6.76         ((r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X16))
% 6.56/6.76          | ~ (r2_hidden @ X14 @ X16)
% 6.56/6.76          | ~ (r2_hidden @ X12 @ X13))),
% 6.56/6.76      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.56/6.76  thf('38', plain,
% 6.56/6.76      (![X0 : $i, X1 : $i]:
% 6.56/6.76         (~ (r2_hidden @ X1 @ X0)
% 6.56/6.76          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C_1 @ sk_A @ sk_B)) @ 
% 6.56/6.76             (k2_zfmisc_1 @ X0 @ sk_B)))),
% 6.56/6.76      inference('sup-', [status(thm)], ['36', '37'])).
% 6.56/6.76  thf('39', plain,
% 6.56/6.76      ((r2_hidden @ 
% 6.56/6.76        (k4_tarski @ (sk_C_1 @ sk_A @ sk_B) @ (sk_C_1 @ sk_A @ sk_B)) @ 
% 6.56/6.76        (k2_zfmisc_1 @ sk_B @ sk_B))),
% 6.56/6.76      inference('sup-', [status(thm)], ['35', '38'])).
% 6.56/6.76  thf('40', plain,
% 6.56/6.76      (((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_zfmisc_1 @ sk_B @ sk_B))),
% 6.56/6.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.56/6.76  thf('41', plain,
% 6.56/6.76      ((r2_hidden @ 
% 6.56/6.76        (k4_tarski @ (sk_C_1 @ sk_A @ sk_B) @ (sk_C_1 @ sk_A @ sk_B)) @ 
% 6.56/6.76        (k2_zfmisc_1 @ sk_A @ sk_A))),
% 6.56/6.76      inference('demod', [status(thm)], ['39', '40'])).
% 6.56/6.76  thf('42', plain,
% 6.56/6.76      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 6.56/6.76         ((r2_hidden @ X12 @ X13)
% 6.56/6.76          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X15)))),
% 6.56/6.76      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.56/6.76  thf('43', plain, ((r2_hidden @ (sk_C_1 @ sk_A @ sk_B) @ sk_A)),
% 6.56/6.76      inference('sup-', [status(thm)], ['41', '42'])).
% 6.56/6.76  thf('44', plain,
% 6.56/6.76      (![X10 : $i, X11 : $i]:
% 6.56/6.76         (((X11) = (X10))
% 6.56/6.76          | ~ (r2_hidden @ (sk_C_1 @ X10 @ X11) @ X10)
% 6.56/6.76          | ~ (r2_hidden @ (sk_C_1 @ X10 @ X11) @ X11))),
% 6.56/6.76      inference('cnf', [status(esa)], [t2_tarski])).
% 6.56/6.76  thf('45', plain,
% 6.56/6.76      ((~ (r2_hidden @ (sk_C_1 @ sk_A @ sk_B) @ sk_B) | ((sk_B) = (sk_A)))),
% 6.56/6.76      inference('sup-', [status(thm)], ['43', '44'])).
% 6.56/6.76  thf('46', plain, ((r2_hidden @ (sk_C_1 @ sk_A @ sk_B) @ sk_B)),
% 6.56/6.76      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 6.56/6.76  thf('47', plain, (((sk_B) = (sk_A))),
% 6.56/6.76      inference('demod', [status(thm)], ['45', '46'])).
% 6.56/6.76  thf('48', plain, (((sk_A) != (sk_B))),
% 6.56/6.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.56/6.76  thf('49', plain, ($false),
% 6.56/6.76      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 6.56/6.76  
% 6.56/6.76  % SZS output end Refutation
% 6.56/6.76  
% 6.56/6.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
