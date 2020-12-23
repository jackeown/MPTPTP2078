%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1eAFFNymrD

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:10 EST 2020

% Result     : Theorem 43.32s
% Output     : Refutation 43.32s
% Verified   : 
% Statistics : Number of formulae       :   75 (  88 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  586 ( 744 expanded)
%              Number of equality atoms :   53 (  64 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(t47_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t47_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k3_xboole_0 @ X20 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( o_0_0_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( o_0_0_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('39',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ ( k3_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1eAFFNymrD
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 43.32/43.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 43.32/43.59  % Solved by: fo/fo7.sh
% 43.32/43.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 43.32/43.59  % done 16102 iterations in 43.136s
% 43.32/43.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 43.32/43.59  % SZS output start Refutation
% 43.32/43.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 43.32/43.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 43.32/43.59  thf(sk_B_type, type, sk_B: $i).
% 43.32/43.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 43.32/43.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 43.32/43.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 43.32/43.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 43.32/43.59  thf(sk_A_type, type, sk_A: $i).
% 43.32/43.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 43.32/43.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 43.32/43.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 43.32/43.59  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 43.32/43.59  thf(t47_xboole_1, conjecture,
% 43.32/43.59    (![A:$i,B:$i]:
% 43.32/43.59     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 43.32/43.59  thf(zf_stmt_0, negated_conjecture,
% 43.32/43.59    (~( ![A:$i,B:$i]:
% 43.32/43.59        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 43.32/43.59          ( k4_xboole_0 @ A @ B ) ) )),
% 43.32/43.59    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 43.32/43.59  thf('0', plain,
% 43.32/43.59      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 43.32/43.59         != (k4_xboole_0 @ sk_A @ sk_B))),
% 43.32/43.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.32/43.59  thf(commutativity_k3_xboole_0, axiom,
% 43.32/43.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 43.32/43.59  thf('1', plain,
% 43.32/43.59      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 43.32/43.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 43.32/43.59  thf('2', plain,
% 43.32/43.59      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 43.32/43.59         != (k4_xboole_0 @ sk_A @ sk_B))),
% 43.32/43.59      inference('demod', [status(thm)], ['0', '1'])).
% 43.32/43.59  thf(t36_xboole_1, axiom,
% 43.32/43.59    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 43.32/43.59  thf('3', plain,
% 43.32/43.59      (![X30 : $i, X31 : $i]: (r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X30)),
% 43.32/43.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 43.32/43.59  thf(t28_xboole_1, axiom,
% 43.32/43.59    (![A:$i,B:$i]:
% 43.32/43.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 43.32/43.59  thf('4', plain,
% 43.32/43.59      (![X28 : $i, X29 : $i]:
% 43.32/43.59         (((k3_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_tarski @ X28 @ X29))),
% 43.32/43.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 43.32/43.59  thf('5', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 43.32/43.59           = (k4_xboole_0 @ X0 @ X1))),
% 43.32/43.59      inference('sup-', [status(thm)], ['3', '4'])).
% 43.32/43.59  thf('6', plain,
% 43.32/43.59      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 43.32/43.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 43.32/43.59  thf('7', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 43.32/43.59           = (k4_xboole_0 @ X0 @ X1))),
% 43.32/43.59      inference('demod', [status(thm)], ['5', '6'])).
% 43.32/43.59  thf(t3_xboole_0, axiom,
% 43.32/43.59    (![A:$i,B:$i]:
% 43.32/43.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 43.32/43.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 43.32/43.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 43.32/43.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 43.32/43.59  thf('8', plain,
% 43.32/43.59      (![X13 : $i, X14 : $i]:
% 43.32/43.59         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 43.32/43.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 43.32/43.59  thf('9', plain,
% 43.32/43.59      (![X13 : $i, X14 : $i]:
% 43.32/43.59         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 43.32/43.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 43.32/43.59  thf(d5_xboole_0, axiom,
% 43.32/43.59    (![A:$i,B:$i,C:$i]:
% 43.32/43.59     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 43.32/43.59       ( ![D:$i]:
% 43.32/43.59         ( ( r2_hidden @ D @ C ) <=>
% 43.32/43.59           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 43.32/43.59  thf('10', plain,
% 43.32/43.59      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 43.32/43.59         (~ (r2_hidden @ X8 @ X7)
% 43.32/43.59          | ~ (r2_hidden @ X8 @ X6)
% 43.32/43.59          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 43.32/43.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 43.32/43.59  thf('11', plain,
% 43.32/43.59      (![X5 : $i, X6 : $i, X8 : $i]:
% 43.32/43.59         (~ (r2_hidden @ X8 @ X6)
% 43.32/43.59          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 43.32/43.59      inference('simplify', [status(thm)], ['10'])).
% 43.32/43.59  thf('12', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.32/43.59         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 43.32/43.59          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 43.32/43.59      inference('sup-', [status(thm)], ['9', '11'])).
% 43.32/43.59  thf('13', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 43.32/43.59          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 43.32/43.59      inference('sup-', [status(thm)], ['8', '12'])).
% 43.32/43.59  thf('14', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 43.32/43.59      inference('simplify', [status(thm)], ['13'])).
% 43.32/43.59  thf(d7_xboole_0, axiom,
% 43.32/43.59    (![A:$i,B:$i]:
% 43.32/43.59     ( ( r1_xboole_0 @ A @ B ) <=>
% 43.32/43.59       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 43.32/43.59  thf('15', plain,
% 43.32/43.59      (![X10 : $i, X11 : $i]:
% 43.32/43.59         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 43.32/43.59          | ~ (r1_xboole_0 @ X10 @ X11))),
% 43.32/43.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.32/43.59  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 43.32/43.59  thf('16', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 43.32/43.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 43.32/43.59  thf('17', plain,
% 43.32/43.59      (![X10 : $i, X11 : $i]:
% 43.32/43.59         (((k3_xboole_0 @ X10 @ X11) = (o_0_0_xboole_0))
% 43.32/43.59          | ~ (r1_xboole_0 @ X10 @ X11))),
% 43.32/43.59      inference('demod', [status(thm)], ['15', '16'])).
% 43.32/43.59  thf('18', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (o_0_0_xboole_0))),
% 43.32/43.59      inference('sup-', [status(thm)], ['14', '17'])).
% 43.32/43.59  thf('19', plain,
% 43.32/43.59      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 43.32/43.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 43.32/43.59  thf('20', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 43.32/43.59      inference('demod', [status(thm)], ['18', '19'])).
% 43.32/43.59  thf(t16_xboole_1, axiom,
% 43.32/43.59    (![A:$i,B:$i,C:$i]:
% 43.32/43.59     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 43.32/43.59       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 43.32/43.59  thf('21', plain,
% 43.32/43.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 43.32/43.59         ((k3_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22)
% 43.32/43.59           = (k3_xboole_0 @ X20 @ (k3_xboole_0 @ X21 @ X22)))),
% 43.32/43.59      inference('cnf', [status(esa)], [t16_xboole_1])).
% 43.32/43.59  thf('22', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.32/43.59         ((o_0_0_xboole_0)
% 43.32/43.59           = (k3_xboole_0 @ X1 @ 
% 43.32/43.59              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))))),
% 43.32/43.59      inference('sup+', [status(thm)], ['20', '21'])).
% 43.32/43.59  thf('23', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((o_0_0_xboole_0)
% 43.32/43.59           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 43.32/43.59      inference('sup+', [status(thm)], ['7', '22'])).
% 43.32/43.59  thf('24', plain,
% 43.32/43.59      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 43.32/43.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 43.32/43.59  thf('25', plain,
% 43.32/43.59      (![X10 : $i, X12 : $i]:
% 43.32/43.59         ((r1_xboole_0 @ X10 @ X12)
% 43.32/43.59          | ((k3_xboole_0 @ X10 @ X12) != (k1_xboole_0)))),
% 43.32/43.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.32/43.59  thf('26', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 43.32/43.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 43.32/43.59  thf('27', plain,
% 43.32/43.59      (![X10 : $i, X12 : $i]:
% 43.32/43.59         ((r1_xboole_0 @ X10 @ X12)
% 43.32/43.59          | ((k3_xboole_0 @ X10 @ X12) != (o_0_0_xboole_0)))),
% 43.32/43.59      inference('demod', [status(thm)], ['25', '26'])).
% 43.32/43.59  thf('28', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         (((k3_xboole_0 @ X1 @ X0) != (o_0_0_xboole_0))
% 43.32/43.59          | (r1_xboole_0 @ X0 @ X1))),
% 43.32/43.59      inference('sup-', [status(thm)], ['24', '27'])).
% 43.32/43.59  thf('29', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 43.32/43.59          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 43.32/43.59      inference('sup-', [status(thm)], ['23', '28'])).
% 43.32/43.59  thf('30', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X1)),
% 43.32/43.59      inference('simplify', [status(thm)], ['29'])).
% 43.32/43.59  thf('31', plain,
% 43.32/43.59      (![X5 : $i, X6 : $i, X9 : $i]:
% 43.32/43.59         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 43.32/43.59          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 43.32/43.59          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 43.32/43.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 43.32/43.59  thf('32', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 43.32/43.59          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 43.32/43.59      inference('eq_fact', [status(thm)], ['31'])).
% 43.32/43.59  thf('33', plain,
% 43.32/43.59      (![X5 : $i, X6 : $i, X9 : $i]:
% 43.32/43.59         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 43.32/43.59          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 43.32/43.59          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 43.32/43.59          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 43.32/43.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 43.32/43.59  thf('34', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 43.32/43.59          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 43.32/43.59          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 43.32/43.59          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 43.32/43.59      inference('sup-', [status(thm)], ['32', '33'])).
% 43.32/43.59  thf('35', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 43.32/43.59          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 43.32/43.59          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 43.32/43.59      inference('simplify', [status(thm)], ['34'])).
% 43.32/43.59  thf('36', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 43.32/43.59          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 43.32/43.59      inference('eq_fact', [status(thm)], ['31'])).
% 43.32/43.59  thf('37', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 43.32/43.59          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 43.32/43.59      inference('clc', [status(thm)], ['35', '36'])).
% 43.32/43.59  thf('38', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 43.32/43.59          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 43.32/43.59      inference('eq_fact', [status(thm)], ['31'])).
% 43.32/43.59  thf('39', plain,
% 43.32/43.59      (![X13 : $i, X15 : $i, X16 : $i]:
% 43.32/43.59         (~ (r2_hidden @ X15 @ X13)
% 43.32/43.59          | ~ (r2_hidden @ X15 @ X16)
% 43.32/43.59          | ~ (r1_xboole_0 @ X13 @ X16))),
% 43.32/43.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 43.32/43.59  thf('40', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.32/43.59         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 43.32/43.59          | ~ (r1_xboole_0 @ X0 @ X2)
% 43.32/43.59          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2))),
% 43.32/43.59      inference('sup-', [status(thm)], ['38', '39'])).
% 43.32/43.59  thf('41', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         (((X1) = (k4_xboole_0 @ X1 @ X0))
% 43.32/43.59          | ~ (r1_xboole_0 @ X1 @ X0)
% 43.32/43.59          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 43.32/43.59      inference('sup-', [status(thm)], ['37', '40'])).
% 43.32/43.59  thf('42', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         (~ (r1_xboole_0 @ X1 @ X0) | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 43.32/43.59      inference('simplify', [status(thm)], ['41'])).
% 43.32/43.59  thf('43', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 43.32/43.59           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 43.32/43.59      inference('sup-', [status(thm)], ['30', '42'])).
% 43.32/43.59  thf(t41_xboole_1, axiom,
% 43.32/43.59    (![A:$i,B:$i,C:$i]:
% 43.32/43.59     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 43.32/43.59       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 43.32/43.59  thf('44', plain,
% 43.32/43.59      (![X34 : $i, X35 : $i, X36 : $i]:
% 43.32/43.59         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 43.32/43.59           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 43.32/43.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 43.32/43.59  thf(commutativity_k2_xboole_0, axiom,
% 43.32/43.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 43.32/43.59  thf('45', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 43.32/43.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 43.32/43.59  thf(t22_xboole_1, axiom,
% 43.32/43.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 43.32/43.59  thf('46', plain,
% 43.32/43.59      (![X26 : $i, X27 : $i]:
% 43.32/43.59         ((k2_xboole_0 @ X26 @ (k3_xboole_0 @ X26 @ X27)) = (X26))),
% 43.32/43.59      inference('cnf', [status(esa)], [t22_xboole_1])).
% 43.32/43.59  thf('47', plain,
% 43.32/43.59      (![X0 : $i, X1 : $i]:
% 43.32/43.59         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 43.32/43.59           = (k4_xboole_0 @ X1 @ X0))),
% 43.32/43.59      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 43.32/43.59  thf('48', plain,
% 43.32/43.59      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 43.32/43.59      inference('demod', [status(thm)], ['2', '47'])).
% 43.32/43.59  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 43.32/43.59  
% 43.32/43.59  % SZS output end Refutation
% 43.32/43.59  
% 43.32/43.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
