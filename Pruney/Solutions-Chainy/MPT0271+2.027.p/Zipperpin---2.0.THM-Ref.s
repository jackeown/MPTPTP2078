%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UJoVK3rwpM

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:24 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 120 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  537 ( 907 expanded)
%              Number of equality atoms :   63 ( 106 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X51: $i,X53: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X51 ) @ X53 )
        = ( k1_tarski @ X51 ) )
      | ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('5',plain,
    ( ( ( k1_xboole_0
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t50_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf('8',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X56 @ X57 ) @ X58 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t50_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','35'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('38',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','44'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','13','14','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UJoVK3rwpM
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.16/1.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.16/1.36  % Solved by: fo/fo7.sh
% 1.16/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.16/1.36  % done 1521 iterations in 0.902s
% 1.16/1.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.16/1.36  % SZS output start Refutation
% 1.16/1.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.16/1.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.16/1.36  thf(sk_B_type, type, sk_B: $i).
% 1.16/1.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.16/1.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.16/1.36  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.16/1.36  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.16/1.36  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.16/1.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.16/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.16/1.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.16/1.36  thf(t68_zfmisc_1, conjecture,
% 1.16/1.36    (![A:$i,B:$i]:
% 1.16/1.36     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 1.16/1.36       ( r2_hidden @ A @ B ) ))).
% 1.16/1.36  thf(zf_stmt_0, negated_conjecture,
% 1.16/1.36    (~( ![A:$i,B:$i]:
% 1.16/1.36        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 1.16/1.36          ( r2_hidden @ A @ B ) ) )),
% 1.16/1.36    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 1.16/1.36  thf('0', plain,
% 1.16/1.36      ((~ (r2_hidden @ sk_A @ sk_B)
% 1.16/1.36        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 1.16/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.36  thf('1', plain,
% 1.16/1.36      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.16/1.36       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.16/1.36      inference('split', [status(esa)], ['0'])).
% 1.16/1.36  thf('2', plain,
% 1.16/1.36      (((r2_hidden @ sk_A @ sk_B)
% 1.16/1.36        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.16/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.36  thf('3', plain,
% 1.16/1.36      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 1.16/1.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.16/1.36      inference('split', [status(esa)], ['2'])).
% 1.16/1.36  thf(l33_zfmisc_1, axiom,
% 1.16/1.36    (![A:$i,B:$i]:
% 1.16/1.36     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 1.16/1.36       ( ~( r2_hidden @ A @ B ) ) ))).
% 1.16/1.36  thf('4', plain,
% 1.16/1.36      (![X51 : $i, X53 : $i]:
% 1.16/1.36         (((k4_xboole_0 @ (k1_tarski @ X51) @ X53) = (k1_tarski @ X51))
% 1.16/1.36          | (r2_hidden @ X51 @ X53))),
% 1.16/1.36      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 1.16/1.36  thf('5', plain,
% 1.16/1.36      (((((k1_xboole_0) = (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 1.16/1.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.16/1.36      inference('sup+', [status(thm)], ['3', '4'])).
% 1.16/1.36  thf(t69_enumset1, axiom,
% 1.16/1.36    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.16/1.36  thf('6', plain, (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 1.16/1.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.16/1.36  thf(t1_boole, axiom,
% 1.16/1.36    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.16/1.36  thf('7', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.16/1.36      inference('cnf', [status(esa)], [t1_boole])).
% 1.16/1.36  thf(t50_zfmisc_1, axiom,
% 1.16/1.36    (![A:$i,B:$i,C:$i]:
% 1.16/1.36     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 1.16/1.36  thf('8', plain,
% 1.16/1.36      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.16/1.36         ((k2_xboole_0 @ (k2_tarski @ X56 @ X57) @ X58) != (k1_xboole_0))),
% 1.16/1.36      inference('cnf', [status(esa)], [t50_zfmisc_1])).
% 1.16/1.36  thf('9', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 1.16/1.36      inference('sup-', [status(thm)], ['7', '8'])).
% 1.16/1.36  thf('10', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 1.16/1.36      inference('sup-', [status(thm)], ['6', '9'])).
% 1.16/1.36  thf('11', plain,
% 1.16/1.36      (((r2_hidden @ sk_A @ sk_B))
% 1.16/1.36         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.16/1.36      inference('simplify_reflect-', [status(thm)], ['5', '10'])).
% 1.16/1.36  thf('12', plain,
% 1.16/1.36      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.16/1.36      inference('split', [status(esa)], ['0'])).
% 1.16/1.36  thf('13', plain,
% 1.16/1.36      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.16/1.36       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.16/1.36      inference('sup-', [status(thm)], ['11', '12'])).
% 1.16/1.36  thf('14', plain,
% 1.16/1.36      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.16/1.36       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.20/1.36      inference('split', [status(esa)], ['2'])).
% 1.20/1.36  thf('15', plain,
% 1.20/1.36      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.20/1.36      inference('split', [status(esa)], ['2'])).
% 1.20/1.36  thf(d5_xboole_0, axiom,
% 1.20/1.36    (![A:$i,B:$i,C:$i]:
% 1.20/1.36     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.20/1.36       ( ![D:$i]:
% 1.20/1.36         ( ( r2_hidden @ D @ C ) <=>
% 1.20/1.36           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.20/1.36  thf('16', plain,
% 1.20/1.36      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.20/1.36         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.20/1.36          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.20/1.36          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.20/1.36      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.20/1.36  thf('17', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.20/1.36      inference('cnf', [status(esa)], [t1_boole])).
% 1.20/1.36  thf(t95_xboole_1, axiom,
% 1.20/1.36    (![A:$i,B:$i]:
% 1.20/1.36     ( ( k3_xboole_0 @ A @ B ) =
% 1.20/1.36       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.20/1.36  thf('18', plain,
% 1.20/1.36      (![X16 : $i, X17 : $i]:
% 1.20/1.36         ((k3_xboole_0 @ X16 @ X17)
% 1.20/1.36           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 1.20/1.36              (k2_xboole_0 @ X16 @ X17)))),
% 1.20/1.36      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.20/1.36  thf(commutativity_k5_xboole_0, axiom,
% 1.20/1.36    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.20/1.36  thf('19', plain,
% 1.20/1.36      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.20/1.36      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.20/1.36  thf('20', plain,
% 1.20/1.36      (![X16 : $i, X17 : $i]:
% 1.20/1.36         ((k3_xboole_0 @ X16 @ X17)
% 1.20/1.36           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 1.20/1.36              (k5_xboole_0 @ X16 @ X17)))),
% 1.20/1.36      inference('demod', [status(thm)], ['18', '19'])).
% 1.20/1.36  thf('21', plain,
% 1.20/1.36      (![X0 : $i]:
% 1.20/1.36         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 1.20/1.36           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.20/1.36      inference('sup+', [status(thm)], ['17', '20'])).
% 1.20/1.36  thf(t5_boole, axiom,
% 1.20/1.36    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.20/1.36  thf('22', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.20/1.36      inference('cnf', [status(esa)], [t5_boole])).
% 1.20/1.36  thf('23', plain,
% 1.20/1.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.20/1.36      inference('demod', [status(thm)], ['21', '22'])).
% 1.20/1.36  thf(t92_xboole_1, axiom,
% 1.20/1.36    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.20/1.36  thf('24', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 1.20/1.36      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.20/1.36  thf('25', plain,
% 1.20/1.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.20/1.36      inference('demod', [status(thm)], ['23', '24'])).
% 1.20/1.36  thf(t100_xboole_1, axiom,
% 1.20/1.36    (![A:$i,B:$i]:
% 1.20/1.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.20/1.36  thf('26', plain,
% 1.20/1.36      (![X8 : $i, X9 : $i]:
% 1.20/1.36         ((k4_xboole_0 @ X8 @ X9)
% 1.20/1.36           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.20/1.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.20/1.36  thf('27', plain,
% 1.20/1.36      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.20/1.36      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.20/1.36  thf('28', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.20/1.36      inference('cnf', [status(esa)], [t5_boole])).
% 1.20/1.36  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.20/1.36      inference('sup+', [status(thm)], ['27', '28'])).
% 1.20/1.36  thf('30', plain,
% 1.20/1.36      (![X0 : $i]:
% 1.20/1.36         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.20/1.36      inference('sup+', [status(thm)], ['26', '29'])).
% 1.20/1.36  thf('31', plain,
% 1.20/1.36      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.20/1.36         (~ (r2_hidden @ X6 @ X5)
% 1.20/1.36          | ~ (r2_hidden @ X6 @ X4)
% 1.20/1.36          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.20/1.36      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.20/1.36  thf('32', plain,
% 1.20/1.36      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.20/1.36         (~ (r2_hidden @ X6 @ X4)
% 1.20/1.36          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.20/1.36      inference('simplify', [status(thm)], ['31'])).
% 1.20/1.36  thf('33', plain,
% 1.20/1.36      (![X0 : $i, X1 : $i]:
% 1.20/1.36         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 1.20/1.36          | ~ (r2_hidden @ X1 @ X0))),
% 1.20/1.36      inference('sup-', [status(thm)], ['30', '32'])).
% 1.20/1.36  thf('34', plain,
% 1.20/1.36      (![X0 : $i]:
% 1.20/1.36         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 1.20/1.36      inference('sup-', [status(thm)], ['25', '33'])).
% 1.20/1.36  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.20/1.36      inference('simplify', [status(thm)], ['34'])).
% 1.20/1.36  thf('36', plain,
% 1.20/1.36      (![X0 : $i, X1 : $i]:
% 1.20/1.36         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.20/1.36          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.20/1.36      inference('sup-', [status(thm)], ['16', '35'])).
% 1.20/1.36  thf(d1_tarski, axiom,
% 1.20/1.36    (![A:$i,B:$i]:
% 1.20/1.36     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.20/1.36       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.20/1.36  thf('37', plain,
% 1.20/1.36      (![X18 : $i, X20 : $i, X21 : $i]:
% 1.20/1.36         (~ (r2_hidden @ X21 @ X20)
% 1.20/1.36          | ((X21) = (X18))
% 1.20/1.36          | ((X20) != (k1_tarski @ X18)))),
% 1.20/1.36      inference('cnf', [status(esa)], [d1_tarski])).
% 1.20/1.36  thf('38', plain,
% 1.20/1.36      (![X18 : $i, X21 : $i]:
% 1.20/1.36         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 1.20/1.36      inference('simplify', [status(thm)], ['37'])).
% 1.20/1.36  thf('39', plain,
% 1.20/1.36      (![X0 : $i, X1 : $i]:
% 1.20/1.36         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.20/1.36          | ((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.20/1.36      inference('sup-', [status(thm)], ['36', '38'])).
% 1.20/1.36  thf('40', plain,
% 1.20/1.36      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.20/1.36         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.20/1.36          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.20/1.36          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.20/1.36      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.20/1.36  thf('41', plain,
% 1.20/1.36      (![X0 : $i, X1 : $i]:
% 1.20/1.36         (~ (r2_hidden @ X0 @ X1)
% 1.20/1.36          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.20/1.36          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 1.20/1.36             k1_xboole_0)
% 1.20/1.36          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.20/1.36      inference('sup-', [status(thm)], ['39', '40'])).
% 1.20/1.36  thf('42', plain,
% 1.20/1.36      (![X0 : $i, X1 : $i]:
% 1.20/1.36         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 1.20/1.36           k1_xboole_0)
% 1.20/1.36          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.20/1.36          | ~ (r2_hidden @ X0 @ X1))),
% 1.20/1.36      inference('simplify', [status(thm)], ['41'])).
% 1.20/1.36  thf('43', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.20/1.36      inference('simplify', [status(thm)], ['34'])).
% 1.20/1.36  thf('44', plain,
% 1.20/1.36      (![X0 : $i, X1 : $i]:
% 1.20/1.36         (~ (r2_hidden @ X0 @ X1)
% 1.20/1.36          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.20/1.36      inference('clc', [status(thm)], ['42', '43'])).
% 1.20/1.36  thf('45', plain,
% 1.20/1.36      ((((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 1.20/1.36         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.20/1.36      inference('sup-', [status(thm)], ['15', '44'])).
% 1.20/1.36  thf('46', plain,
% 1.20/1.36      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 1.20/1.36         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.20/1.36      inference('split', [status(esa)], ['0'])).
% 1.20/1.36  thf('47', plain,
% 1.20/1.36      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.20/1.36         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 1.20/1.36             ((r2_hidden @ sk_A @ sk_B)))),
% 1.20/1.36      inference('sup-', [status(thm)], ['45', '46'])).
% 1.20/1.36  thf('48', plain,
% 1.20/1.36      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.20/1.36       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.20/1.36      inference('simplify', [status(thm)], ['47'])).
% 1.20/1.36  thf('49', plain, ($false),
% 1.20/1.36      inference('sat_resolution*', [status(thm)], ['1', '13', '14', '48'])).
% 1.20/1.36  
% 1.20/1.36  % SZS output end Refutation
% 1.20/1.36  
% 1.20/1.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
