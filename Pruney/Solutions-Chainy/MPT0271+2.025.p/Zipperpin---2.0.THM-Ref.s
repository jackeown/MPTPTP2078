%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NkUE35XA7z

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:24 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 138 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  520 (1040 expanded)
%              Number of equality atoms :   53 ( 108 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X31 != X30 )
      | ( r2_hidden @ X31 @ X32 )
      | ( X32
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X30: $i] :
      ( r2_hidden @ X30 @ ( k1_tarski @ X30 ) ) ),
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

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( X33 = X30 )
      | ( X32
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('35',plain,(
    ! [X30: $i,X33: $i] :
      ( ( X33 = X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ X2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['26'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['26'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NkUE35XA7z
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 1.38/1.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.38/1.57  % Solved by: fo/fo7.sh
% 1.38/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.57  % done 2528 iterations in 1.124s
% 1.38/1.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.38/1.57  % SZS output start Refutation
% 1.38/1.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.38/1.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.38/1.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.38/1.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.38/1.57  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.38/1.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.38/1.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.38/1.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.38/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.57  thf(t68_zfmisc_1, conjecture,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 1.38/1.57       ( r2_hidden @ A @ B ) ))).
% 1.38/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.57    (~( ![A:$i,B:$i]:
% 1.38/1.57        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 1.38/1.57          ( r2_hidden @ A @ B ) ) )),
% 1.38/1.57    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 1.38/1.57  thf('0', plain,
% 1.38/1.57      ((~ (r2_hidden @ sk_A @ sk_B)
% 1.38/1.57        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf('1', plain,
% 1.38/1.57      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.38/1.57       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.38/1.57      inference('split', [status(esa)], ['0'])).
% 1.38/1.57  thf('2', plain,
% 1.38/1.57      (((r2_hidden @ sk_A @ sk_B)
% 1.38/1.57        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf('3', plain,
% 1.38/1.57      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 1.38/1.57         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.38/1.57      inference('split', [status(esa)], ['2'])).
% 1.38/1.57  thf(d1_tarski, axiom,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.38/1.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.38/1.57  thf('4', plain,
% 1.38/1.57      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.38/1.57         (((X31) != (X30))
% 1.38/1.57          | (r2_hidden @ X31 @ X32)
% 1.38/1.57          | ((X32) != (k1_tarski @ X30)))),
% 1.38/1.57      inference('cnf', [status(esa)], [d1_tarski])).
% 1.38/1.57  thf('5', plain, (![X30 : $i]: (r2_hidden @ X30 @ (k1_tarski @ X30))),
% 1.38/1.57      inference('simplify', [status(thm)], ['4'])).
% 1.38/1.57  thf(d5_xboole_0, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i]:
% 1.38/1.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.38/1.57       ( ![D:$i]:
% 1.38/1.57         ( ( r2_hidden @ D @ C ) <=>
% 1.38/1.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.38/1.57  thf('6', plain,
% 1.38/1.57      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.38/1.57         (~ (r2_hidden @ X2 @ X3)
% 1.38/1.57          | (r2_hidden @ X2 @ X4)
% 1.38/1.57          | (r2_hidden @ X2 @ X5)
% 1.38/1.57          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.38/1.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.57  thf('7', plain,
% 1.38/1.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.38/1.57         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 1.38/1.57          | (r2_hidden @ X2 @ X4)
% 1.38/1.57          | ~ (r2_hidden @ X2 @ X3))),
% 1.38/1.57      inference('simplify', [status(thm)], ['6'])).
% 1.38/1.57  thf('8', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         ((r2_hidden @ X0 @ X1)
% 1.38/1.57          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['5', '7'])).
% 1.38/1.57  thf('9', plain,
% 1.38/1.57      ((((r2_hidden @ sk_A @ k1_xboole_0) | (r2_hidden @ sk_A @ sk_B)))
% 1.38/1.57         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.38/1.57      inference('sup+', [status(thm)], ['3', '8'])).
% 1.38/1.57  thf(commutativity_k5_xboole_0, axiom,
% 1.38/1.57    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.38/1.57  thf('10', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.38/1.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.38/1.57  thf(t5_boole, axiom,
% 1.38/1.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.38/1.57  thf('11', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.38/1.57      inference('cnf', [status(esa)], [t5_boole])).
% 1.38/1.57  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.38/1.57      inference('sup+', [status(thm)], ['10', '11'])).
% 1.38/1.57  thf(t98_xboole_1, axiom,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.38/1.57  thf('13', plain,
% 1.38/1.57      (![X28 : $i, X29 : $i]:
% 1.38/1.57         ((k2_xboole_0 @ X28 @ X29)
% 1.38/1.57           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 1.38/1.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.38/1.57  thf('14', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.38/1.57      inference('sup+', [status(thm)], ['12', '13'])).
% 1.38/1.57  thf(t1_boole, axiom,
% 1.38/1.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.38/1.57  thf('15', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.38/1.57      inference('cnf', [status(esa)], [t1_boole])).
% 1.38/1.57  thf(d10_xboole_0, axiom,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.38/1.57  thf('16', plain,
% 1.38/1.57      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.38/1.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.38/1.57  thf('17', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.38/1.57      inference('simplify', [status(thm)], ['16'])).
% 1.38/1.57  thf(t10_xboole_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i]:
% 1.38/1.57     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.38/1.57  thf('18', plain,
% 1.38/1.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.38/1.57         (~ (r1_tarski @ X13 @ X14)
% 1.38/1.57          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 1.38/1.57      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.38/1.57  thf('19', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.38/1.57      inference('sup-', [status(thm)], ['17', '18'])).
% 1.38/1.57  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.38/1.57      inference('sup+', [status(thm)], ['15', '19'])).
% 1.38/1.57  thf(t12_xboole_1, axiom,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.38/1.57  thf('21', plain,
% 1.38/1.57      (![X16 : $i, X17 : $i]:
% 1.38/1.57         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 1.38/1.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.38/1.57  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.38/1.57      inference('sup-', [status(thm)], ['20', '21'])).
% 1.38/1.57  thf('23', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.38/1.57      inference('demod', [status(thm)], ['14', '22'])).
% 1.38/1.57  thf('24', plain,
% 1.38/1.57      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.38/1.57         (~ (r2_hidden @ X6 @ X5)
% 1.38/1.57          | ~ (r2_hidden @ X6 @ X4)
% 1.38/1.57          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.38/1.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.57  thf('25', plain,
% 1.38/1.57      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.38/1.57         (~ (r2_hidden @ X6 @ X4)
% 1.38/1.57          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.38/1.57      inference('simplify', [status(thm)], ['24'])).
% 1.38/1.57  thf('26', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.38/1.57      inference('sup-', [status(thm)], ['23', '25'])).
% 1.38/1.57  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.38/1.57      inference('condensation', [status(thm)], ['26'])).
% 1.38/1.57  thf('28', plain,
% 1.38/1.57      (((r2_hidden @ sk_A @ sk_B))
% 1.38/1.57         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.38/1.57      inference('clc', [status(thm)], ['9', '27'])).
% 1.38/1.57  thf('29', plain,
% 1.38/1.57      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.38/1.57      inference('split', [status(esa)], ['0'])).
% 1.38/1.57  thf('30', plain,
% 1.38/1.57      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.38/1.57       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['28', '29'])).
% 1.38/1.57  thf('31', plain,
% 1.38/1.57      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.38/1.57       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.38/1.57      inference('split', [status(esa)], ['2'])).
% 1.38/1.57  thf('32', plain,
% 1.38/1.57      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.38/1.57      inference('split', [status(esa)], ['2'])).
% 1.38/1.57  thf('33', plain,
% 1.38/1.57      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.38/1.57         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.38/1.57          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.38/1.57          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.38/1.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.57  thf('34', plain,
% 1.38/1.57      (![X30 : $i, X32 : $i, X33 : $i]:
% 1.38/1.57         (~ (r2_hidden @ X33 @ X32)
% 1.38/1.57          | ((X33) = (X30))
% 1.38/1.57          | ((X32) != (k1_tarski @ X30)))),
% 1.38/1.57      inference('cnf', [status(esa)], [d1_tarski])).
% 1.38/1.57  thf('35', plain,
% 1.38/1.57      (![X30 : $i, X33 : $i]:
% 1.38/1.57         (((X33) = (X30)) | ~ (r2_hidden @ X33 @ (k1_tarski @ X30)))),
% 1.38/1.57      inference('simplify', [status(thm)], ['34'])).
% 1.38/1.57  thf('36', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.57         ((r2_hidden @ (sk_D @ X2 @ X1 @ (k1_tarski @ X0)) @ X2)
% 1.38/1.57          | ((X2) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.38/1.57          | ((sk_D @ X2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['33', '35'])).
% 1.38/1.57  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.38/1.57      inference('condensation', [status(thm)], ['26'])).
% 1.38/1.57  thf('38', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         (((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.38/1.57          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['36', '37'])).
% 1.38/1.57  thf('39', plain,
% 1.38/1.57      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.38/1.57         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.38/1.57          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.38/1.57          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.38/1.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.57  thf('40', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         (~ (r2_hidden @ X0 @ X1)
% 1.38/1.57          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.38/1.57          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 1.38/1.57             k1_xboole_0)
% 1.38/1.57          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['38', '39'])).
% 1.38/1.57  thf('41', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 1.38/1.57           k1_xboole_0)
% 1.38/1.57          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.38/1.57          | ~ (r2_hidden @ X0 @ X1))),
% 1.38/1.57      inference('simplify', [status(thm)], ['40'])).
% 1.38/1.57  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.38/1.57      inference('condensation', [status(thm)], ['26'])).
% 1.38/1.57  thf('43', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         (~ (r2_hidden @ X0 @ X1)
% 1.38/1.57          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.38/1.57      inference('clc', [status(thm)], ['41', '42'])).
% 1.38/1.57  thf('44', plain,
% 1.38/1.57      ((((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 1.38/1.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['32', '43'])).
% 1.38/1.57  thf('45', plain,
% 1.38/1.57      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 1.38/1.57         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.38/1.57      inference('split', [status(esa)], ['0'])).
% 1.38/1.57  thf('46', plain,
% 1.38/1.57      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.38/1.57         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 1.38/1.57             ((r2_hidden @ sk_A @ sk_B)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['44', '45'])).
% 1.38/1.57  thf('47', plain,
% 1.38/1.57      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.38/1.57       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.38/1.57      inference('simplify', [status(thm)], ['46'])).
% 1.38/1.57  thf('48', plain, ($false),
% 1.38/1.57      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '47'])).
% 1.38/1.57  
% 1.38/1.57  % SZS output end Refutation
% 1.38/1.57  
% 1.38/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
