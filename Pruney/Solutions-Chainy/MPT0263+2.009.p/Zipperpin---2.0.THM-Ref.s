%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hLcWUtSpwo

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:32 EST 2020

% Result     : Theorem 5.30s
% Output     : Refutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :   58 (  86 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  579 ( 984 expanded)
%              Number of equality atoms :   49 (  82 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X20 != X19 )
      | ( r2_hidden @ X20 @ X21 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X19: $i] :
      ( r2_hidden @ X19 @ ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( X22 = X19 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22 = X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k1_tarski @ X1 )
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','28'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ X18 )
      | ( ( k4_xboole_0 @ X16 @ X18 )
       != X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('33',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hLcWUtSpwo
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 5.30/5.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.30/5.52  % Solved by: fo/fo7.sh
% 5.30/5.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.30/5.52  % done 3029 iterations in 5.057s
% 5.30/5.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.30/5.52  % SZS output start Refutation
% 5.30/5.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.30/5.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.30/5.52  thf(sk_B_type, type, sk_B: $i).
% 5.30/5.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.30/5.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.30/5.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.30/5.52  thf(sk_A_type, type, sk_A: $i).
% 5.30/5.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.30/5.52  thf(d1_tarski, axiom,
% 5.30/5.52    (![A:$i,B:$i]:
% 5.30/5.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 5.30/5.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 5.30/5.52  thf('0', plain,
% 5.30/5.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.30/5.52         (((X20) != (X19))
% 5.30/5.52          | (r2_hidden @ X20 @ X21)
% 5.30/5.52          | ((X21) != (k1_tarski @ X19)))),
% 5.30/5.52      inference('cnf', [status(esa)], [d1_tarski])).
% 5.30/5.52  thf('1', plain, (![X19 : $i]: (r2_hidden @ X19 @ (k1_tarski @ X19))),
% 5.30/5.52      inference('simplify', [status(thm)], ['0'])).
% 5.30/5.52  thf(d5_xboole_0, axiom,
% 5.30/5.52    (![A:$i,B:$i,C:$i]:
% 5.30/5.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 5.30/5.52       ( ![D:$i]:
% 5.30/5.52         ( ( r2_hidden @ D @ C ) <=>
% 5.30/5.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 5.30/5.52  thf('2', plain,
% 5.30/5.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.30/5.52         (~ (r2_hidden @ X8 @ X9)
% 5.30/5.52          | (r2_hidden @ X8 @ X10)
% 5.30/5.52          | (r2_hidden @ X8 @ X11)
% 5.30/5.52          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 5.30/5.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.30/5.52  thf('3', plain,
% 5.30/5.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.30/5.52         ((r2_hidden @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 5.30/5.52          | (r2_hidden @ X8 @ X10)
% 5.30/5.52          | ~ (r2_hidden @ X8 @ X9))),
% 5.30/5.52      inference('simplify', [status(thm)], ['2'])).
% 5.30/5.52  thf('4', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         ((r2_hidden @ X0 @ X1)
% 5.30/5.52          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.30/5.52      inference('sup-', [status(thm)], ['1', '3'])).
% 5.30/5.52  thf(d4_xboole_0, axiom,
% 5.30/5.52    (![A:$i,B:$i,C:$i]:
% 5.30/5.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 5.30/5.52       ( ![D:$i]:
% 5.30/5.52         ( ( r2_hidden @ D @ C ) <=>
% 5.30/5.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.30/5.52  thf('5', plain,
% 5.30/5.52      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.30/5.52         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 5.30/5.52          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.30/5.52          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.30/5.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.30/5.52  thf('6', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.30/5.52          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.30/5.52      inference('eq_fact', [status(thm)], ['5'])).
% 5.30/5.52  thf('7', plain,
% 5.30/5.52      (![X19 : $i, X21 : $i, X22 : $i]:
% 5.30/5.52         (~ (r2_hidden @ X22 @ X21)
% 5.30/5.52          | ((X22) = (X19))
% 5.30/5.52          | ((X21) != (k1_tarski @ X19)))),
% 5.30/5.52      inference('cnf', [status(esa)], [d1_tarski])).
% 5.30/5.52  thf('8', plain,
% 5.30/5.52      (![X19 : $i, X22 : $i]:
% 5.30/5.52         (((X22) = (X19)) | ~ (r2_hidden @ X22 @ (k1_tarski @ X19)))),
% 5.30/5.52      inference('simplify', [status(thm)], ['7'])).
% 5.30/5.52  thf('9', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.30/5.52          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 5.30/5.52      inference('sup-', [status(thm)], ['6', '8'])).
% 5.30/5.52  thf('10', plain,
% 5.30/5.52      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.30/5.52         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.30/5.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.30/5.52  thf('11', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         (~ (r2_hidden @ X0 @ X1)
% 5.30/5.52          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 5.30/5.52               (k1_tarski @ X0))
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 5.30/5.52               (k1_tarski @ X0))
% 5.30/5.52          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.30/5.52      inference('sup-', [status(thm)], ['9', '10'])).
% 5.30/5.52  thf('12', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         (~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 5.30/5.52             (k1_tarski @ X0))
% 5.30/5.52          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.30/5.52          | ~ (r2_hidden @ X0 @ X1))),
% 5.30/5.52      inference('simplify', [status(thm)], ['11'])).
% 5.30/5.52  thf('13', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.30/5.52          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.30/5.52      inference('eq_fact', [status(thm)], ['5'])).
% 5.30/5.52  thf('14', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         (~ (r2_hidden @ X0 @ X1)
% 5.30/5.52          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.30/5.52      inference('clc', [status(thm)], ['12', '13'])).
% 5.30/5.52  thf('15', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         ((r2_hidden @ X1 @ X0)
% 5.30/5.52          | ((k1_tarski @ X1)
% 5.30/5.52              = (k3_xboole_0 @ (k1_tarski @ X1) @ 
% 5.30/5.52                 (k4_xboole_0 @ (k1_tarski @ X1) @ X0))))),
% 5.30/5.52      inference('sup-', [status(thm)], ['4', '14'])).
% 5.30/5.52  thf('16', plain,
% 5.30/5.52      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.30/5.52         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 5.30/5.52          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 5.30/5.52          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.30/5.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.30/5.52  thf('17', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.30/5.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.30/5.52      inference('eq_fact', [status(thm)], ['16'])).
% 5.30/5.52  thf('18', plain,
% 5.30/5.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 5.30/5.52         (~ (r2_hidden @ X12 @ X11)
% 5.30/5.52          | (r2_hidden @ X12 @ X9)
% 5.30/5.52          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 5.30/5.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.30/5.52  thf('19', plain,
% 5.30/5.52      (![X9 : $i, X10 : $i, X12 : $i]:
% 5.30/5.52         ((r2_hidden @ X12 @ X9)
% 5.30/5.52          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 5.30/5.52      inference('simplify', [status(thm)], ['18'])).
% 5.30/5.52  thf('20', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.30/5.52         (((k4_xboole_0 @ X1 @ X0)
% 5.30/5.52            = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 5.30/5.52          | (r2_hidden @ 
% 5.30/5.52             (sk_D @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0) @ X2) @ 
% 5.30/5.52             X1))),
% 5.30/5.52      inference('sup-', [status(thm)], ['17', '19'])).
% 5.30/5.52  thf('21', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.30/5.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.30/5.52      inference('eq_fact', [status(thm)], ['16'])).
% 5.30/5.52  thf('22', plain,
% 5.30/5.52      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.30/5.52         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.30/5.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.30/5.52  thf('23', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 5.30/5.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.30/5.52      inference('sup-', [status(thm)], ['21', '22'])).
% 5.30/5.52  thf('24', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.30/5.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.30/5.52      inference('simplify', [status(thm)], ['23'])).
% 5.30/5.52  thf('25', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.30/5.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.30/5.52      inference('eq_fact', [status(thm)], ['16'])).
% 5.30/5.52  thf('26', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 5.30/5.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 5.30/5.52      inference('clc', [status(thm)], ['24', '25'])).
% 5.30/5.52  thf('27', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         (((k4_xboole_0 @ X0 @ X1)
% 5.30/5.52            = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 5.30/5.52          | ((k4_xboole_0 @ X0 @ X1)
% 5.30/5.52              = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 5.30/5.52      inference('sup-', [status(thm)], ['20', '26'])).
% 5.30/5.52  thf('28', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         ((k4_xboole_0 @ X0 @ X1)
% 5.30/5.52           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.30/5.52      inference('simplify', [status(thm)], ['27'])).
% 5.30/5.52  thf('29', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         ((r2_hidden @ X1 @ X0)
% 5.30/5.52          | ((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 5.30/5.52      inference('demod', [status(thm)], ['15', '28'])).
% 5.30/5.52  thf(t83_xboole_1, axiom,
% 5.30/5.52    (![A:$i,B:$i]:
% 5.30/5.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.30/5.52  thf('30', plain,
% 5.30/5.52      (![X16 : $i, X18 : $i]:
% 5.30/5.52         ((r1_xboole_0 @ X16 @ X18) | ((k4_xboole_0 @ X16 @ X18) != (X16)))),
% 5.30/5.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.30/5.52  thf('31', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 5.30/5.52          | (r2_hidden @ X0 @ X1)
% 5.30/5.52          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 5.30/5.52      inference('sup-', [status(thm)], ['29', '30'])).
% 5.30/5.52  thf('32', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 5.30/5.52      inference('simplify', [status(thm)], ['31'])).
% 5.30/5.52  thf(t58_zfmisc_1, conjecture,
% 5.30/5.52    (![A:$i,B:$i]:
% 5.30/5.52     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 5.30/5.52       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 5.30/5.52  thf(zf_stmt_0, negated_conjecture,
% 5.30/5.52    (~( ![A:$i,B:$i]:
% 5.30/5.52        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 5.30/5.52          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 5.30/5.52    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 5.30/5.52  thf('33', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 5.30/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.30/5.52  thf('34', plain, ((r2_hidden @ sk_A @ sk_B)),
% 5.30/5.52      inference('sup-', [status(thm)], ['32', '33'])).
% 5.30/5.52  thf('35', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]:
% 5.30/5.52         (~ (r2_hidden @ X0 @ X1)
% 5.30/5.52          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.30/5.52      inference('clc', [status(thm)], ['12', '13'])).
% 5.30/5.52  thf('36', plain,
% 5.30/5.52      (((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 5.30/5.52      inference('sup-', [status(thm)], ['34', '35'])).
% 5.30/5.52  thf(commutativity_k3_xboole_0, axiom,
% 5.30/5.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.30/5.52  thf('37', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.30/5.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.30/5.52  thf('38', plain,
% 5.30/5.52      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 5.30/5.52      inference('demod', [status(thm)], ['36', '37'])).
% 5.30/5.52  thf('39', plain,
% 5.30/5.52      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 5.30/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.30/5.52  thf('40', plain,
% 5.30/5.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.30/5.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.30/5.52  thf('41', plain,
% 5.30/5.52      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 5.30/5.52      inference('demod', [status(thm)], ['39', '40'])).
% 5.30/5.52  thf('42', plain, ($false),
% 5.30/5.52      inference('simplify_reflect-', [status(thm)], ['38', '41'])).
% 5.30/5.52  
% 5.30/5.52  % SZS output end Refutation
% 5.30/5.52  
% 5.30/5.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
