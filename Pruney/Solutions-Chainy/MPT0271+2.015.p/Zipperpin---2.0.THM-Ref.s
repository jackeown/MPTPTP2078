%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p04IeCdxw8

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:22 EST 2020

% Result     : Theorem 5.56s
% Output     : Refutation 5.56s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 101 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  545 ( 855 expanded)
%              Number of equality atoms :   56 (  92 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
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

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('13',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 != X42 )
      | ~ ( r2_hidden @ X40 @ ( k4_xboole_0 @ X41 @ ( k1_tarski @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('14',plain,(
    ! [X41: $i,X42: $i] :
      ~ ( r2_hidden @ X42 @ ( k4_xboole_0 @ X41 @ ( k1_tarski @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['9','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','43'])).

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
    inference('sat_resolution*',[status(thm)],['1','18','19','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p04IeCdxw8
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.56/5.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.56/5.75  % Solved by: fo/fo7.sh
% 5.56/5.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.56/5.75  % done 7335 iterations in 5.288s
% 5.56/5.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.56/5.75  % SZS output start Refutation
% 5.56/5.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.56/5.75  thf(sk_B_type, type, sk_B: $i).
% 5.56/5.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.56/5.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.56/5.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.56/5.75  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.56/5.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.56/5.75  thf(sk_A_type, type, sk_A: $i).
% 5.56/5.75  thf(t68_zfmisc_1, conjecture,
% 5.56/5.75    (![A:$i,B:$i]:
% 5.56/5.75     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 5.56/5.75       ( r2_hidden @ A @ B ) ))).
% 5.56/5.75  thf(zf_stmt_0, negated_conjecture,
% 5.56/5.75    (~( ![A:$i,B:$i]:
% 5.56/5.75        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 5.56/5.75          ( r2_hidden @ A @ B ) ) )),
% 5.56/5.75    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 5.56/5.75  thf('0', plain,
% 5.56/5.75      ((~ (r2_hidden @ sk_A @ sk_B)
% 5.56/5.75        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 5.56/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.75  thf('1', plain,
% 5.56/5.75      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 5.56/5.75       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 5.56/5.75      inference('split', [status(esa)], ['0'])).
% 5.56/5.75  thf('2', plain,
% 5.56/5.75      (((r2_hidden @ sk_A @ sk_B)
% 5.56/5.75        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 5.56/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.75  thf('3', plain,
% 5.56/5.75      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 5.56/5.75         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 5.56/5.75      inference('split', [status(esa)], ['2'])).
% 5.56/5.75  thf(d1_tarski, axiom,
% 5.56/5.75    (![A:$i,B:$i]:
% 5.56/5.75     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 5.56/5.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 5.56/5.75  thf('4', plain,
% 5.56/5.75      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.56/5.75         (((X19) != (X18))
% 5.56/5.75          | (r2_hidden @ X19 @ X20)
% 5.56/5.75          | ((X20) != (k1_tarski @ X18)))),
% 5.56/5.75      inference('cnf', [status(esa)], [d1_tarski])).
% 5.56/5.75  thf('5', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 5.56/5.75      inference('simplify', [status(thm)], ['4'])).
% 5.56/5.75  thf(d5_xboole_0, axiom,
% 5.56/5.75    (![A:$i,B:$i,C:$i]:
% 5.56/5.75     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 5.56/5.75       ( ![D:$i]:
% 5.56/5.75         ( ( r2_hidden @ D @ C ) <=>
% 5.56/5.75           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 5.56/5.75  thf('6', plain,
% 5.56/5.75      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.56/5.75         (~ (r2_hidden @ X2 @ X3)
% 5.56/5.75          | (r2_hidden @ X2 @ X4)
% 5.56/5.75          | (r2_hidden @ X2 @ X5)
% 5.56/5.75          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 5.56/5.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.56/5.75  thf('7', plain,
% 5.56/5.75      (![X2 : $i, X3 : $i, X4 : $i]:
% 5.56/5.75         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 5.56/5.75          | (r2_hidden @ X2 @ X4)
% 5.56/5.75          | ~ (r2_hidden @ X2 @ X3))),
% 5.56/5.75      inference('simplify', [status(thm)], ['6'])).
% 5.56/5.75  thf('8', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i]:
% 5.56/5.75         ((r2_hidden @ X0 @ X1)
% 5.56/5.75          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.56/5.75      inference('sup-', [status(thm)], ['5', '7'])).
% 5.56/5.75  thf('9', plain,
% 5.56/5.75      ((((r2_hidden @ sk_A @ k1_xboole_0) | (r2_hidden @ sk_A @ sk_B)))
% 5.56/5.75         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 5.56/5.75      inference('sup+', [status(thm)], ['3', '8'])).
% 5.56/5.75  thf(t1_boole, axiom,
% 5.56/5.75    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.56/5.75  thf('10', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 5.56/5.75      inference('cnf', [status(esa)], [t1_boole])).
% 5.56/5.75  thf(t46_xboole_1, axiom,
% 5.56/5.75    (![A:$i,B:$i]:
% 5.56/5.75     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 5.56/5.75  thf('11', plain,
% 5.56/5.75      (![X13 : $i, X14 : $i]:
% 5.56/5.75         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 5.56/5.75      inference('cnf', [status(esa)], [t46_xboole_1])).
% 5.56/5.75  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.56/5.75      inference('sup+', [status(thm)], ['10', '11'])).
% 5.56/5.75  thf(t64_zfmisc_1, axiom,
% 5.56/5.75    (![A:$i,B:$i,C:$i]:
% 5.56/5.75     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 5.56/5.75       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 5.56/5.75  thf('13', plain,
% 5.56/5.75      (![X40 : $i, X41 : $i, X42 : $i]:
% 5.56/5.75         (((X40) != (X42))
% 5.56/5.75          | ~ (r2_hidden @ X40 @ (k4_xboole_0 @ X41 @ (k1_tarski @ X42))))),
% 5.56/5.75      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 5.56/5.75  thf('14', plain,
% 5.56/5.75      (![X41 : $i, X42 : $i]:
% 5.56/5.75         ~ (r2_hidden @ X42 @ (k4_xboole_0 @ X41 @ (k1_tarski @ X42)))),
% 5.56/5.75      inference('simplify', [status(thm)], ['13'])).
% 5.56/5.75  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.56/5.75      inference('sup-', [status(thm)], ['12', '14'])).
% 5.56/5.75  thf('16', plain,
% 5.56/5.75      (((r2_hidden @ sk_A @ sk_B))
% 5.56/5.75         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 5.56/5.75      inference('clc', [status(thm)], ['9', '15'])).
% 5.56/5.75  thf('17', plain,
% 5.56/5.75      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 5.56/5.75      inference('split', [status(esa)], ['0'])).
% 5.56/5.75  thf('18', plain,
% 5.56/5.75      (((r2_hidden @ sk_A @ sk_B)) | 
% 5.56/5.75       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 5.56/5.75      inference('sup-', [status(thm)], ['16', '17'])).
% 5.56/5.75  thf('19', plain,
% 5.56/5.75      (((r2_hidden @ sk_A @ sk_B)) | 
% 5.56/5.75       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 5.56/5.75      inference('split', [status(esa)], ['2'])).
% 5.56/5.75  thf('20', plain,
% 5.56/5.75      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.56/5.75      inference('split', [status(esa)], ['2'])).
% 5.56/5.75  thf('21', plain,
% 5.56/5.75      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.56/5.75         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.56/5.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.56/5.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.56/5.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.56/5.75  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.56/5.75      inference('sup-', [status(thm)], ['12', '14'])).
% 5.56/5.75  thf('23', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i]:
% 5.56/5.75         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 5.56/5.75          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 5.56/5.75      inference('sup-', [status(thm)], ['21', '22'])).
% 5.56/5.75  thf(t4_boole, axiom,
% 5.56/5.75    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 5.56/5.75  thf('24', plain,
% 5.56/5.75      (![X15 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 5.56/5.75      inference('cnf', [status(esa)], [t4_boole])).
% 5.56/5.75  thf('25', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i]:
% 5.56/5.75         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 5.56/5.75          | ((X1) = (k1_xboole_0)))),
% 5.56/5.75      inference('demod', [status(thm)], ['23', '24'])).
% 5.56/5.75  thf('26', plain,
% 5.56/5.75      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.56/5.75         (~ (r2_hidden @ X6 @ X5)
% 5.56/5.75          | (r2_hidden @ X6 @ X3)
% 5.56/5.75          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 5.56/5.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.56/5.75  thf('27', plain,
% 5.56/5.75      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.56/5.75         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 5.56/5.75      inference('simplify', [status(thm)], ['26'])).
% 5.56/5.75  thf('28', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.56/5.75         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 5.56/5.75          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 5.56/5.75             X1))),
% 5.56/5.75      inference('sup-', [status(thm)], ['25', '27'])).
% 5.56/5.75  thf('29', plain,
% 5.56/5.75      (![X18 : $i, X20 : $i, X21 : $i]:
% 5.56/5.75         (~ (r2_hidden @ X21 @ X20)
% 5.56/5.75          | ((X21) = (X18))
% 5.56/5.75          | ((X20) != (k1_tarski @ X18)))),
% 5.56/5.75      inference('cnf', [status(esa)], [d1_tarski])).
% 5.56/5.75  thf('30', plain,
% 5.56/5.75      (![X18 : $i, X21 : $i]:
% 5.56/5.75         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 5.56/5.75      inference('simplify', [status(thm)], ['29'])).
% 5.56/5.75  thf('31', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.56/5.75         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 5.56/5.75          | ((sk_D @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ k1_xboole_0)
% 5.56/5.75              = (X0)))),
% 5.56/5.75      inference('sup-', [status(thm)], ['28', '30'])).
% 5.56/5.75  thf('32', plain,
% 5.56/5.75      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.56/5.75         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.56/5.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.56/5.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.56/5.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.56/5.75  thf('33', plain,
% 5.56/5.75      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.56/5.75         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.56/5.75          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 5.56/5.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.56/5.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.56/5.75  thf('34', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i]:
% 5.56/5.75         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 5.56/5.75          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 5.56/5.75          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 5.56/5.75          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 5.56/5.75      inference('sup-', [status(thm)], ['32', '33'])).
% 5.56/5.75  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.56/5.75      inference('sup+', [status(thm)], ['10', '11'])).
% 5.56/5.75  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.56/5.75      inference('sup+', [status(thm)], ['10', '11'])).
% 5.56/5.75  thf('37', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i]:
% 5.56/5.75         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 5.56/5.75          | ((X1) = (k1_xboole_0))
% 5.56/5.75          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 5.56/5.75          | ((X1) = (k1_xboole_0)))),
% 5.56/5.75      inference('demod', [status(thm)], ['34', '35', '36'])).
% 5.56/5.75  thf('38', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i]:
% 5.56/5.75         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 5.56/5.75      inference('simplify', [status(thm)], ['37'])).
% 5.56/5.75  thf('39', plain,
% 5.56/5.75      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.56/5.75         (~ (r2_hidden @ X6 @ X5)
% 5.56/5.75          | ~ (r2_hidden @ X6 @ X4)
% 5.56/5.75          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 5.56/5.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.56/5.75  thf('40', plain,
% 5.56/5.75      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.56/5.75         (~ (r2_hidden @ X6 @ X4)
% 5.56/5.75          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 5.56/5.75      inference('simplify', [status(thm)], ['39'])).
% 5.56/5.75  thf('41', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.56/5.75         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 5.56/5.75          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 5.56/5.75      inference('sup-', [status(thm)], ['38', '40'])).
% 5.56/5.75  thf('42', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i]:
% 5.56/5.75         (~ (r2_hidden @ X0 @ X1)
% 5.56/5.75          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 5.56/5.75          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 5.56/5.75      inference('sup-', [status(thm)], ['31', '41'])).
% 5.56/5.75  thf('43', plain,
% 5.56/5.75      (![X0 : $i, X1 : $i]:
% 5.56/5.75         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 5.56/5.75          | ~ (r2_hidden @ X0 @ X1))),
% 5.56/5.75      inference('simplify', [status(thm)], ['42'])).
% 5.56/5.75  thf('44', plain,
% 5.56/5.75      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 5.56/5.75         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.56/5.75      inference('sup-', [status(thm)], ['20', '43'])).
% 5.56/5.75  thf('45', plain,
% 5.56/5.75      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 5.56/5.75         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 5.56/5.75      inference('split', [status(esa)], ['0'])).
% 5.56/5.75  thf('46', plain,
% 5.56/5.75      ((((k1_xboole_0) != (k1_xboole_0)))
% 5.56/5.75         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 5.56/5.75             ((r2_hidden @ sk_A @ sk_B)))),
% 5.56/5.75      inference('sup-', [status(thm)], ['44', '45'])).
% 5.56/5.75  thf('47', plain,
% 5.56/5.75      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 5.56/5.75       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 5.56/5.75      inference('simplify', [status(thm)], ['46'])).
% 5.56/5.75  thf('48', plain, ($false),
% 5.56/5.75      inference('sat_resolution*', [status(thm)], ['1', '18', '19', '47'])).
% 5.56/5.75  
% 5.56/5.75  % SZS output end Refutation
% 5.56/5.75  
% 5.56/5.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
