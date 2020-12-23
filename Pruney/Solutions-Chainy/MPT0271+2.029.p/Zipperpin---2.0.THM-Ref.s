%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9KFOQmvPaE

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  98 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  432 ( 788 expanded)
%              Number of equality atoms :   44 (  83 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X13 != X12 )
      | ( r2_hidden @ X13 @ X14 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_tarski @ X12 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( r2_hidden @ sk_A @ k1_xboole_0 )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['19'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('28',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['19'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','21','22','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9KFOQmvPaE
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:29:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 191 iterations in 0.099s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(t68_zfmisc_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55       ( r2_hidden @ A @ B ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55          ( r2_hidden @ A @ B ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.55        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.55       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ sk_B)
% 0.20/0.55        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.20/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf(d1_tarski, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.55         (((X13) != (X12))
% 0.20/0.55          | (r2_hidden @ X13 @ X14)
% 0.20/0.55          | ((X14) != (k1_tarski @ X12)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.55  thf('5', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_tarski @ X12))),
% 0.20/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.55  thf(d5_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.55       ( ![D:$i]:
% 0.20/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.55          | (r2_hidden @ X2 @ X4)
% 0.20/0.55          | (r2_hidden @ X2 @ X5)
% 0.20/0.55          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.55         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.20/0.55          | (r2_hidden @ X2 @ X4)
% 0.20/0.55          | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ X1)
% 0.20/0.55          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((((r2_hidden @ sk_A @ k1_xboole_0) | (r2_hidden @ sk_A @ sk_B)))
% 0.20/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['3', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ k1_xboole_0))
% 0.20/0.55         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.20/0.55             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf(t2_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.55  thf(t100_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X8 @ X9)
% 0.20/0.55           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf(t5_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.55  thf('15', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.55  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.55          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.55          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.55          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.55  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.55      inference('condensation', [status(thm)], ['19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.55       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.55       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.20/0.55         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.20/0.55          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.20/0.55          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.55  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.55      inference('condensation', [status(thm)], ['19'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.20/0.55          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X15 @ X14)
% 0.20/0.55          | ((X15) = (X12))
% 0.20/0.55          | ((X14) != (k1_tarski @ X12)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X12 : $i, X15 : $i]:
% 0.20/0.55         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.20/0.55          | ((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.20/0.55         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.20/0.55          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.55          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.20/0.55          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 0.20/0.55             k1_xboole_0)
% 0.20/0.55          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 0.20/0.55           k1_xboole_0)
% 0.20/0.55          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.55  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.55      inference('condensation', [status(thm)], ['19'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.55          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.20/0.55      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      ((((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.20/0.55         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.55         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.20/0.55             ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.55       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.55  thf('39', plain, ($false),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['1', '21', '22', '38'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
