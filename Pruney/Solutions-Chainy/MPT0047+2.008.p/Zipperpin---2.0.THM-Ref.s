%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KjaGl8tCxt

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:03 EST 2020

% Result     : Theorem 16.42s
% Output     : Refutation 16.42s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 108 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  602 ( 832 expanded)
%              Number of equality atoms :   51 (  73 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t40_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = ( k4_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t40_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('14',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

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

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','40'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','43'])).

thf('45',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t33_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ( r1_tarski @ ( k4_xboole_0 @ X25 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t33_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KjaGl8tCxt
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:01:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 16.42/16.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 16.42/16.63  % Solved by: fo/fo7.sh
% 16.42/16.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.42/16.63  % done 14944 iterations in 16.179s
% 16.42/16.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 16.42/16.63  % SZS output start Refutation
% 16.42/16.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 16.42/16.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 16.42/16.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 16.42/16.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 16.42/16.63  thf(sk_A_type, type, sk_A: $i).
% 16.42/16.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 16.42/16.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 16.42/16.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 16.42/16.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 16.42/16.63  thf(sk_B_type, type, sk_B: $i).
% 16.42/16.63  thf(t40_xboole_1, conjecture,
% 16.42/16.63    (![A:$i,B:$i]:
% 16.42/16.63     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 16.42/16.63  thf(zf_stmt_0, negated_conjecture,
% 16.42/16.63    (~( ![A:$i,B:$i]:
% 16.42/16.63        ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) =
% 16.42/16.63          ( k4_xboole_0 @ A @ B ) ) )),
% 16.42/16.63    inference('cnf.neg', [status(esa)], [t40_xboole_1])).
% 16.42/16.63  thf('0', plain,
% 16.42/16.63      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 16.42/16.63         != (k4_xboole_0 @ sk_A @ sk_B))),
% 16.42/16.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.42/16.63  thf(t39_xboole_1, axiom,
% 16.42/16.63    (![A:$i,B:$i]:
% 16.42/16.63     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 16.42/16.63  thf('1', plain,
% 16.42/16.63      (![X30 : $i, X31 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30))
% 16.42/16.63           = (k2_xboole_0 @ X30 @ X31))),
% 16.42/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.42/16.63  thf(commutativity_k2_xboole_0, axiom,
% 16.42/16.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 16.42/16.63  thf('2', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.42/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.42/16.63  thf('3', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.42/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.42/16.63  thf(t7_xboole_1, axiom,
% 16.42/16.63    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 16.42/16.63  thf('4', plain,
% 16.42/16.63      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 16.42/16.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 16.42/16.63  thf('5', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 16.42/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.42/16.63  thf(t12_xboole_1, axiom,
% 16.42/16.63    (![A:$i,B:$i]:
% 16.42/16.63     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 16.42/16.63  thf('6', plain,
% 16.42/16.63      (![X17 : $i, X18 : $i]:
% 16.42/16.63         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 16.42/16.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 16.42/16.63  thf('7', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 16.42/16.63           = (k2_xboole_0 @ X1 @ X0))),
% 16.42/16.63      inference('sup-', [status(thm)], ['5', '6'])).
% 16.42/16.63  thf('8', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.42/16.63           = (k2_xboole_0 @ X0 @ X1))),
% 16.42/16.63      inference('sup+', [status(thm)], ['2', '7'])).
% 16.42/16.63  thf('9', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.42/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 16.42/16.63      inference('sup+', [status(thm)], ['1', '8'])).
% 16.42/16.63  thf('10', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.42/16.63           = (k2_xboole_0 @ X0 @ X1))),
% 16.42/16.63      inference('sup+', [status(thm)], ['2', '7'])).
% 16.42/16.63  thf('11', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.42/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.42/16.63  thf('12', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X0 @ X1)
% 16.42/16.63           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 16.42/16.63      inference('demod', [status(thm)], ['9', '10', '11'])).
% 16.42/16.63  thf('13', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.42/16.63           = (k2_xboole_0 @ X0 @ X1))),
% 16.42/16.63      inference('sup+', [status(thm)], ['2', '7'])).
% 16.42/16.63  thf('14', plain,
% 16.42/16.63      (![X30 : $i, X31 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30))
% 16.42/16.63           = (k2_xboole_0 @ X30 @ X31))),
% 16.42/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.42/16.63  thf('15', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.42/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.42/16.63  thf(t21_xboole_1, axiom,
% 16.42/16.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 16.42/16.63  thf('16', plain,
% 16.42/16.63      (![X20 : $i, X21 : $i]:
% 16.42/16.63         ((k3_xboole_0 @ X20 @ (k2_xboole_0 @ X20 @ X21)) = (X20))),
% 16.42/16.63      inference('cnf', [status(esa)], [t21_xboole_1])).
% 16.42/16.63  thf('17', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 16.42/16.63      inference('sup+', [status(thm)], ['15', '16'])).
% 16.42/16.63  thf('18', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 16.42/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.42/16.63      inference('sup+', [status(thm)], ['14', '17'])).
% 16.42/16.63  thf(commutativity_k3_xboole_0, axiom,
% 16.42/16.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 16.42/16.63  thf('19', plain,
% 16.42/16.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 16.42/16.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 16.42/16.63  thf('20', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 16.42/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.42/16.63      inference('demod', [status(thm)], ['18', '19'])).
% 16.42/16.63  thf('21', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 16.42/16.63           (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 16.42/16.63           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 16.42/16.63      inference('sup+', [status(thm)], ['13', '20'])).
% 16.42/16.63  thf('22', plain,
% 16.42/16.63      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 16.42/16.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 16.42/16.63  thf('23', plain,
% 16.42/16.63      (![X17 : $i, X18 : $i]:
% 16.42/16.63         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 16.42/16.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 16.42/16.63  thf('24', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.42/16.63           = (k2_xboole_0 @ X1 @ X0))),
% 16.42/16.63      inference('sup-', [status(thm)], ['22', '23'])).
% 16.42/16.63  thf(t24_xboole_1, axiom,
% 16.42/16.63    (![A:$i,B:$i,C:$i]:
% 16.42/16.63     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 16.42/16.63       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 16.42/16.63  thf('25', plain,
% 16.42/16.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X22 @ (k3_xboole_0 @ X23 @ X24))
% 16.42/16.63           = (k3_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ 
% 16.42/16.63              (k2_xboole_0 @ X22 @ X24)))),
% 16.42/16.63      inference('cnf', [status(esa)], [t24_xboole_1])).
% 16.42/16.63  thf('26', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 16.42/16.63           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X2)))),
% 16.42/16.63      inference('sup+', [status(thm)], ['24', '25'])).
% 16.42/16.63  thf('27', plain,
% 16.42/16.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X22 @ (k3_xboole_0 @ X23 @ X24))
% 16.42/16.63           = (k3_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ 
% 16.42/16.63              (k2_xboole_0 @ X22 @ X24)))),
% 16.42/16.63      inference('cnf', [status(esa)], [t24_xboole_1])).
% 16.42/16.63  thf('28', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 16.42/16.63           = (k2_xboole_0 @ X2 @ (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 16.42/16.63      inference('sup+', [status(thm)], ['26', '27'])).
% 16.42/16.63  thf('29', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X1 @ 
% 16.42/16.63           (k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))
% 16.42/16.63           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 16.42/16.63      inference('sup+', [status(thm)], ['21', '28'])).
% 16.42/16.63  thf(t3_xboole_0, axiom,
% 16.42/16.63    (![A:$i,B:$i]:
% 16.42/16.63     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 16.42/16.63            ( r1_xboole_0 @ A @ B ) ) ) & 
% 16.42/16.63       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 16.42/16.63            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 16.42/16.63  thf('30', plain,
% 16.42/16.63      (![X13 : $i, X14 : $i]:
% 16.42/16.63         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 16.42/16.63      inference('cnf', [status(esa)], [t3_xboole_0])).
% 16.42/16.63  thf('31', plain,
% 16.42/16.63      (![X13 : $i, X14 : $i]:
% 16.42/16.63         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 16.42/16.63      inference('cnf', [status(esa)], [t3_xboole_0])).
% 16.42/16.63  thf(d5_xboole_0, axiom,
% 16.42/16.63    (![A:$i,B:$i,C:$i]:
% 16.42/16.63     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 16.42/16.63       ( ![D:$i]:
% 16.42/16.63         ( ( r2_hidden @ D @ C ) <=>
% 16.42/16.63           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 16.42/16.63  thf('32', plain,
% 16.42/16.63      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 16.42/16.63         (~ (r2_hidden @ X8 @ X7)
% 16.42/16.63          | ~ (r2_hidden @ X8 @ X6)
% 16.42/16.63          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 16.42/16.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 16.42/16.63  thf('33', plain,
% 16.42/16.63      (![X5 : $i, X6 : $i, X8 : $i]:
% 16.42/16.63         (~ (r2_hidden @ X8 @ X6)
% 16.42/16.63          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 16.42/16.63      inference('simplify', [status(thm)], ['32'])).
% 16.42/16.63  thf('34', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.42/16.63         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 16.42/16.63          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 16.42/16.63      inference('sup-', [status(thm)], ['31', '33'])).
% 16.42/16.63  thf('35', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 16.42/16.63          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 16.42/16.63      inference('sup-', [status(thm)], ['30', '34'])).
% 16.42/16.63  thf('36', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 16.42/16.63      inference('simplify', [status(thm)], ['35'])).
% 16.42/16.63  thf(d7_xboole_0, axiom,
% 16.42/16.63    (![A:$i,B:$i]:
% 16.42/16.63     ( ( r1_xboole_0 @ A @ B ) <=>
% 16.42/16.63       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 16.42/16.63  thf('37', plain,
% 16.42/16.63      (![X10 : $i, X11 : $i]:
% 16.42/16.63         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 16.42/16.63          | ~ (r1_xboole_0 @ X10 @ X11))),
% 16.42/16.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 16.42/16.63  thf('38', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 16.42/16.63      inference('sup-', [status(thm)], ['36', '37'])).
% 16.42/16.63  thf('39', plain,
% 16.42/16.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 16.42/16.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 16.42/16.63  thf('40', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 16.42/16.63      inference('demod', [status(thm)], ['38', '39'])).
% 16.42/16.63  thf('41', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 16.42/16.63           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 16.42/16.63      inference('demod', [status(thm)], ['29', '40'])).
% 16.42/16.63  thf(t1_boole, axiom,
% 16.42/16.63    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 16.42/16.63  thf('42', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 16.42/16.63      inference('cnf', [status(esa)], [t1_boole])).
% 16.42/16.63  thf('43', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((X1)
% 16.42/16.63           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 16.42/16.63      inference('demod', [status(thm)], ['41', '42'])).
% 16.42/16.63  thf('44', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.42/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.42/16.63              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 16.42/16.63      inference('sup+', [status(thm)], ['12', '43'])).
% 16.42/16.63  thf('45', plain,
% 16.42/16.63      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 16.42/16.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 16.42/16.63  thf(t33_xboole_1, axiom,
% 16.42/16.63    (![A:$i,B:$i,C:$i]:
% 16.42/16.63     ( ( r1_tarski @ A @ B ) =>
% 16.42/16.63       ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 16.42/16.63  thf('46', plain,
% 16.42/16.63      (![X25 : $i, X26 : $i, X27 : $i]:
% 16.42/16.63         (~ (r1_tarski @ X25 @ X26)
% 16.42/16.63          | (r1_tarski @ (k4_xboole_0 @ X25 @ X27) @ (k4_xboole_0 @ X26 @ X27)))),
% 16.42/16.63      inference('cnf', [status(esa)], [t33_xboole_1])).
% 16.42/16.63  thf('47', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.42/16.63         (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ 
% 16.42/16.63          (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 16.42/16.63      inference('sup-', [status(thm)], ['45', '46'])).
% 16.42/16.63  thf('48', plain,
% 16.42/16.63      (![X17 : $i, X18 : $i]:
% 16.42/16.63         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 16.42/16.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 16.42/16.63  thf('49', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.42/16.63         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 16.42/16.63           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 16.42/16.63           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 16.42/16.63      inference('sup-', [status(thm)], ['47', '48'])).
% 16.42/16.63  thf('50', plain,
% 16.42/16.63      (![X0 : $i, X1 : $i]:
% 16.42/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.42/16.63           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 16.42/16.63      inference('demod', [status(thm)], ['44', '49'])).
% 16.42/16.63  thf('51', plain,
% 16.42/16.63      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 16.42/16.63      inference('demod', [status(thm)], ['0', '50'])).
% 16.42/16.63  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 16.42/16.63  
% 16.42/16.63  % SZS output end Refutation
% 16.42/16.63  
% 16.42/16.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
