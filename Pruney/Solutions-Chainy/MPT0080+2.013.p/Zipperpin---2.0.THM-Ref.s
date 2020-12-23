%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o0D65WCsFd

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:05 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   75 (  98 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   18
%              Number of atoms          :  509 ( 701 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('23',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_C_1
    = ( k2_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','38'])).

thf('40',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('42',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('45',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('48',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('50',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o0D65WCsFd
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 430 iterations in 0.172s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.62  thf(t73_xboole_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.39/0.62       ( r1_tarski @ A @ B ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.62        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.39/0.62            ( r1_xboole_0 @ A @ C ) ) =>
% 0.39/0.62          ( r1_tarski @ A @ B ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.39/0.62  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(d3_tarski, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X3 : $i, X5 : $i]:
% 0.39/0.62         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.62  thf(d5_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.39/0.62       ( ![D:$i]:
% 0.39/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.62           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X10 @ X9)
% 0.39/0.62          | (r2_hidden @ X10 @ X7)
% 0.39/0.62          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.39/0.62         ((r2_hidden @ X10 @ X7)
% 0.39/0.62          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.39/0.62          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '3'])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X3 : $i, X5 : $i]:
% 0.39/0.62         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.39/0.62          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.39/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      (![X3 : $i, X5 : $i]:
% 0.39/0.62         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.62  thf('9', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t12_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.39/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.39/0.62         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.62  thf(t40_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (![X19 : $i, X20 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 0.39/0.62           = (k4_xboole_0 @ X19 @ X20))),
% 0.39/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ 
% 0.39/0.62         (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.39/0.62         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.39/0.62         ((r2_hidden @ X10 @ X7)
% 0.39/0.62          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ 
% 0.39/0.62             (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.39/0.62          | (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X10 @ X9)
% 0.39/0.62          | ~ (r2_hidden @ X10 @ X8)
% 0.39/0.62          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X10 @ X8)
% 0.39/0.62          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ~ (r2_hidden @ X0 @ 
% 0.39/0.62            (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.39/0.62      inference('clc', [status(thm)], ['15', '17'])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)) @ X0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['8', '18'])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.39/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ 
% 0.39/0.62           (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)) @ X0) = (
% 0.39/0.62           X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.62  thf(t1_boole, axiom,
% 0.39/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.62  thf('22', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['21', '22'])).
% 0.39/0.62  thf(t41_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.62       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.39/0.62           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.62  thf(t39_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X17 : $i, X18 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.39/0.62           = (k2_xboole_0 @ X17 @ X18))),
% 0.39/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.62  thf('26', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.39/0.62           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['24', '25'])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (((k2_xboole_0 @ sk_C_1 @ k1_xboole_0)
% 0.39/0.62         = (k2_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['23', '26'])).
% 0.39/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf('30', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.62  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['29', '30'])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (((sk_C_1) = (k2_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['27', '28', '31'])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf(t7_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.39/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.62  thf(t67_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.39/0.62         ( r1_xboole_0 @ B @ C ) ) =>
% 0.39/0.62       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.62         (((X24) = (k1_xboole_0))
% 0.39/0.62          | ~ (r1_tarski @ X24 @ X25)
% 0.39/0.62          | ~ (r1_tarski @ X24 @ X26)
% 0.39/0.62          | ~ (r1_xboole_0 @ X25 @ X26))),
% 0.39/0.62      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         (~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.39/0.62          | ~ (r1_tarski @ X0 @ X2)
% 0.39/0.62          | ((X0) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 0.39/0.62          | ((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.39/0.62          | ~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['32', '37'])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      ((((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.39/0.62        | ~ (r1_xboole_0 @ sk_C_1 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['7', '38'])).
% 0.39/0.62  thf('40', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(symmetry_r1_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i]:
% 0.39/0.62         ((r1_xboole_0 @ X12 @ X13) | ~ (r1_xboole_0 @ X13 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.62  thf('42', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.39/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.62  thf('43', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.39/0.62      inference('demod', [status(thm)], ['39', '42'])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (![X17 : $i, X18 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.39/0.62           = (k2_xboole_0 @ X17 @ X18))),
% 0.39/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup+', [status(thm)], ['43', '44'])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['29', '30'])).
% 0.39/0.62  thf('48', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.62  thf('50', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.62      inference('sup+', [status(thm)], ['48', '49'])).
% 0.39/0.62  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
