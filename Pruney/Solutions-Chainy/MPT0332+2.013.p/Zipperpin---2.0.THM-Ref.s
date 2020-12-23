%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pJc59kyFNu

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:08 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 155 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :   22
%              Number of atoms          :  480 (1079 expanded)
%              Number of equality atoms :   50 ( 121 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t145_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( r2_hidden @ X22 @ X21 )
      | ( X21
        = ( k4_xboole_0 @ X21 @ ( k2_tarski @ X20 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('2',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t99_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) @ ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k5_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) @ ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('36',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','39'])).

thf('41',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','40'])).

thf('42',plain,
    ( ( sk_C
     != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( r2_hidden @ X22 @ X21 )
      | ( X21
        = ( k4_xboole_0 @ X21 @ ( k2_tarski @ X20 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('44',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pJc59kyFNu
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:51:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.31/1.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.31/1.51  % Solved by: fo/fo7.sh
% 1.31/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.31/1.51  % done 665 iterations in 1.051s
% 1.31/1.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.31/1.51  % SZS output start Refutation
% 1.31/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.31/1.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.31/1.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.31/1.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.31/1.51  thf(sk_C_type, type, sk_C: $i).
% 1.31/1.51  thf(sk_B_type, type, sk_B: $i).
% 1.31/1.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.31/1.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.31/1.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.31/1.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.31/1.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.31/1.51  thf(t145_zfmisc_1, conjecture,
% 1.31/1.51    (![A:$i,B:$i,C:$i]:
% 1.31/1.51     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.31/1.51          ( ( C ) !=
% 1.31/1.51            ( k4_xboole_0 @
% 1.31/1.51              ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 1.31/1.51              ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.31/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.31/1.51    (~( ![A:$i,B:$i,C:$i]:
% 1.31/1.51        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.31/1.51             ( ( C ) !=
% 1.31/1.51               ( k4_xboole_0 @
% 1.31/1.51                 ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 1.31/1.51                 ( k2_tarski @ A @ B ) ) ) ) ) )),
% 1.31/1.51    inference('cnf.neg', [status(esa)], [t145_zfmisc_1])).
% 1.31/1.51  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf(t144_zfmisc_1, axiom,
% 1.31/1.51    (![A:$i,B:$i,C:$i]:
% 1.31/1.51     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.31/1.51          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.31/1.51  thf('1', plain,
% 1.31/1.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.31/1.51         ((r2_hidden @ X20 @ X21)
% 1.31/1.51          | (r2_hidden @ X22 @ X21)
% 1.31/1.51          | ((X21) = (k4_xboole_0 @ X21 @ (k2_tarski @ X20 @ X22))))),
% 1.31/1.51      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 1.31/1.51  thf('2', plain,
% 1.31/1.51      (((sk_C)
% 1.31/1.51         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 1.31/1.51             (k2_tarski @ sk_A @ sk_B)))),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf(commutativity_k2_xboole_0, axiom,
% 1.31/1.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.31/1.51  thf('3', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.31/1.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.31/1.51  thf(t98_xboole_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.31/1.51  thf('4', plain,
% 1.31/1.51      (![X13 : $i, X14 : $i]:
% 1.31/1.51         ((k2_xboole_0 @ X13 @ X14)
% 1.31/1.51           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 1.31/1.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.31/1.51  thf('5', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.31/1.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.31/1.51  thf(t99_xboole_1, axiom,
% 1.31/1.51    (![A:$i,B:$i,C:$i]:
% 1.31/1.51     ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.31/1.51       ( k2_xboole_0 @
% 1.31/1.51         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 1.31/1.51         ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ))).
% 1.31/1.51  thf('6', plain,
% 1.31/1.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.31/1.51           = (k2_xboole_0 @ (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)) @ 
% 1.31/1.51              (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X17))))),
% 1.31/1.51      inference('cnf', [status(esa)], [t99_xboole_1])).
% 1.31/1.51  thf(t36_xboole_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.31/1.51  thf('7', plain,
% 1.31/1.51      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.31/1.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.31/1.51  thf(t3_xboole_1, axiom,
% 1.31/1.51    (![A:$i]:
% 1.31/1.51     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.31/1.51  thf('8', plain,
% 1.31/1.51      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 1.31/1.51      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.31/1.51  thf('9', plain,
% 1.31/1.51      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.31/1.51      inference('sup-', [status(thm)], ['7', '8'])).
% 1.31/1.51  thf('10', plain,
% 1.31/1.51      (![X13 : $i, X14 : $i]:
% 1.31/1.51         ((k2_xboole_0 @ X13 @ X14)
% 1.31/1.51           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 1.31/1.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.31/1.51  thf('11', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['9', '10'])).
% 1.31/1.51  thf(t1_boole, axiom,
% 1.31/1.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.31/1.51  thf('12', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.31/1.51      inference('cnf', [status(esa)], [t1_boole])).
% 1.31/1.51  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['11', '12'])).
% 1.31/1.51  thf(t95_xboole_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( k3_xboole_0 @ A @ B ) =
% 1.31/1.51       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.31/1.51  thf('14', plain,
% 1.31/1.51      (![X9 : $i, X10 : $i]:
% 1.31/1.51         ((k3_xboole_0 @ X9 @ X10)
% 1.31/1.51           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 1.31/1.51      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.31/1.51  thf('15', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 1.31/1.51           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['13', '14'])).
% 1.31/1.51  thf(t2_boole, axiom,
% 1.31/1.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.31/1.51  thf('16', plain,
% 1.31/1.51      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.31/1.51      inference('cnf', [status(esa)], [t2_boole])).
% 1.31/1.51  thf('17', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.31/1.51      inference('cnf', [status(esa)], [t1_boole])).
% 1.31/1.51  thf('18', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.31/1.51  thf(t96_xboole_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.31/1.51  thf('19', plain,
% 1.31/1.51      (![X11 : $i, X12 : $i]:
% 1.31/1.51         (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ (k5_xboole_0 @ X11 @ X12))),
% 1.31/1.51      inference('cnf', [status(esa)], [t96_xboole_1])).
% 1.31/1.51  thf('20', plain,
% 1.31/1.51      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0)),
% 1.31/1.51      inference('sup+', [status(thm)], ['18', '19'])).
% 1.31/1.51  thf('21', plain,
% 1.31/1.51      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 1.31/1.51      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.31/1.51  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.31/1.51      inference('sup-', [status(thm)], ['20', '21'])).
% 1.31/1.51  thf('23', plain,
% 1.31/1.51      (![X13 : $i, X14 : $i]:
% 1.31/1.51         ((k2_xboole_0 @ X13 @ X14)
% 1.31/1.51           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 1.31/1.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.31/1.51  thf('24', plain,
% 1.31/1.51      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['22', '23'])).
% 1.31/1.51  thf('25', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['11', '12'])).
% 1.31/1.51  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['24', '25'])).
% 1.31/1.51  thf('27', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 1.31/1.51           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['6', '26'])).
% 1.31/1.51  thf('28', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.31/1.51  thf('29', plain,
% 1.31/1.51      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.31/1.51      inference('sup-', [status(thm)], ['7', '8'])).
% 1.31/1.51  thf('30', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.31/1.51  thf('31', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['5', '30'])).
% 1.31/1.51  thf('32', plain,
% 1.31/1.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.31/1.51           = (k2_xboole_0 @ (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)) @ 
% 1.31/1.51              (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X17))))),
% 1.31/1.51      inference('cnf', [status(esa)], [t99_xboole_1])).
% 1.31/1.51  thf('33', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0)
% 1.31/1.51           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.31/1.51              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['31', '32'])).
% 1.31/1.51  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['24', '25'])).
% 1.31/1.51  thf('35', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.31/1.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.31/1.51  thf('36', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.31/1.51      inference('cnf', [status(esa)], [t1_boole])).
% 1.31/1.51  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['35', '36'])).
% 1.31/1.51  thf('38', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0)
% 1.31/1.51           = (k4_xboole_0 @ X1 @ X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['33', '34', '37'])).
% 1.31/1.51  thf('39', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.31/1.51           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 1.31/1.51      inference('sup+', [status(thm)], ['4', '38'])).
% 1.31/1.51  thf('40', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.31/1.51           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['3', '39'])).
% 1.31/1.51  thf('41', plain,
% 1.31/1.51      (((sk_C)
% 1.31/1.51         != (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 1.31/1.51             (k2_tarski @ sk_A @ sk_B)))),
% 1.31/1.51      inference('demod', [status(thm)], ['2', '40'])).
% 1.31/1.51  thf('42', plain,
% 1.31/1.51      ((((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 1.31/1.51        | (r2_hidden @ sk_B @ sk_C)
% 1.31/1.51        | (r2_hidden @ sk_A @ sk_C))),
% 1.31/1.51      inference('sup-', [status(thm)], ['1', '41'])).
% 1.31/1.51  thf('43', plain,
% 1.31/1.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.31/1.51         ((r2_hidden @ X20 @ X21)
% 1.31/1.51          | (r2_hidden @ X22 @ X21)
% 1.31/1.51          | ((X21) = (k4_xboole_0 @ X21 @ (k2_tarski @ X20 @ X22))))),
% 1.31/1.51      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 1.31/1.51  thf('44', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 1.31/1.51      inference('clc', [status(thm)], ['42', '43'])).
% 1.31/1.51  thf('45', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf('46', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.31/1.51      inference('clc', [status(thm)], ['44', '45'])).
% 1.31/1.51  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 1.31/1.51  
% 1.31/1.51  % SZS output end Refutation
% 1.31/1.51  
% 1.31/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
