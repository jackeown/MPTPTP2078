%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ysGt2Z1qVO

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:16 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 127 expanded)
%              Number of leaves         :   22 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  588 ( 973 expanded)
%              Number of equality atoms :   56 (  97 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t48_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X26 ) @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X26 ) @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( ( k4_xboole_0 @ X16 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','32'])).

thf('34',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('38',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('46',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['4','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ysGt2Z1qVO
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.80  % Solved by: fo/fo7.sh
% 0.60/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.80  % done 995 iterations in 0.349s
% 0.60/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.80  % SZS output start Refutation
% 0.60/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.80  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.80  thf(t48_xboole_1, conjecture,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.60/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.80    (~( ![A:$i,B:$i]:
% 0.60/0.80        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 0.60/0.80          ( k3_xboole_0 @ A @ B ) ) )),
% 0.60/0.80    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 0.60/0.80  thf('0', plain,
% 0.60/0.80      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.60/0.80         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(t47_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.60/0.80  thf('1', plain,
% 0.60/0.80      (![X27 : $i, X28 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28))
% 0.60/0.80           = (k4_xboole_0 @ X27 @ X28))),
% 0.60/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.60/0.80  thf(t39_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.60/0.80  thf('2', plain,
% 0.60/0.80      (![X23 : $i, X24 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.60/0.80           = (k2_xboole_0 @ X23 @ X24))),
% 0.60/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.60/0.80  thf(t40_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.60/0.80  thf('3', plain,
% 0.60/0.80      (![X25 : $i, X26 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X25 @ X26) @ X26)
% 0.60/0.80           = (k4_xboole_0 @ X25 @ X26))),
% 0.60/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.60/0.80  thf('4', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.60/0.80           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['2', '3'])).
% 0.60/0.80  thf(t3_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.60/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.60/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.60/0.80  thf('5', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.80  thf('6', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.80  thf(d5_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.60/0.80       ( ![D:$i]:
% 0.60/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.80           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.60/0.80  thf('7', plain,
% 0.60/0.80      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.80         (~ (r2_hidden @ X6 @ X5)
% 0.60/0.80          | ~ (r2_hidden @ X6 @ X4)
% 0.60/0.80          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.60/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.60/0.80  thf('8', plain,
% 0.60/0.80      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.60/0.80         (~ (r2_hidden @ X6 @ X4)
% 0.60/0.80          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.60/0.80      inference('simplify', [status(thm)], ['7'])).
% 0.60/0.80  thf('9', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.60/0.80          | ~ (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['6', '8'])).
% 0.60/0.80  thf('10', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.60/0.80          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['5', '9'])).
% 0.60/0.80  thf('11', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.60/0.80      inference('simplify', [status(thm)], ['10'])).
% 0.60/0.80  thf('12', plain,
% 0.60/0.80      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.60/0.80         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.60/0.80          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.60/0.80          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.60/0.80  thf('13', plain,
% 0.60/0.80      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.60/0.80         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.60/0.80          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.60/0.80          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.60/0.80  thf('14', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.60/0.80          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.60/0.80          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.60/0.80          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.80  thf(t17_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.60/0.80  thf('15', plain,
% 0.60/0.80      (![X19 : $i, X20 : $i]: (r1_tarski @ (k3_xboole_0 @ X19 @ X20) @ X19)),
% 0.60/0.80      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.60/0.80  thf(l32_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.80  thf('16', plain,
% 0.60/0.80      (![X16 : $i, X18 : $i]:
% 0.60/0.80         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.60/0.80          | ~ (r1_tarski @ X16 @ X18))),
% 0.60/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.60/0.80  thf('17', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.80  thf('18', plain,
% 0.60/0.80      (![X25 : $i, X26 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X25 @ X26) @ X26)
% 0.60/0.80           = (k4_xboole_0 @ X25 @ X26))),
% 0.60/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.60/0.80  thf('19', plain,
% 0.60/0.80      (![X16 : $i, X17 : $i]:
% 0.60/0.80         ((r1_tarski @ X16 @ X17)
% 0.60/0.80          | ((k4_xboole_0 @ X16 @ X17) != (k1_xboole_0)))),
% 0.60/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.60/0.80  thf('20', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.60/0.80          | (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.80  thf('21', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.80          | (r1_tarski @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['17', '20'])).
% 0.60/0.80  thf(commutativity_k2_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.60/0.80  thf('22', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf(t22_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.60/0.80  thf('23', plain,
% 0.60/0.80      (![X21 : $i, X22 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)) = (X21))),
% 0.60/0.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.60/0.80  thf('24', plain,
% 0.60/0.80      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.60/0.80      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.60/0.80  thf('25', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.60/0.80      inference('simplify', [status(thm)], ['24'])).
% 0.60/0.80  thf('26', plain,
% 0.60/0.80      (![X16 : $i, X18 : $i]:
% 0.60/0.80         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.60/0.80          | ~ (r1_tarski @ X16 @ X18))),
% 0.60/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.60/0.80  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['25', '26'])).
% 0.60/0.80  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['25', '26'])).
% 0.60/0.80  thf('29', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.60/0.80          | ((X1) = (k1_xboole_0))
% 0.60/0.80          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.60/0.80          | ((X1) = (k1_xboole_0)))),
% 0.60/0.80      inference('demod', [status(thm)], ['14', '27', '28'])).
% 0.60/0.80  thf('30', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.60/0.80      inference('simplify', [status(thm)], ['29'])).
% 0.60/0.80  thf(t4_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.60/0.80            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.60/0.80  thf('31', plain,
% 0.60/0.80      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.60/0.80         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 0.60/0.80          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.60/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.60/0.80  thf('32', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.80  thf('33', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['11', '32'])).
% 0.60/0.80  thf('34', plain,
% 0.60/0.80      (![X27 : $i, X28 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28))
% 0.60/0.80           = (k4_xboole_0 @ X27 @ X28))),
% 0.60/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.60/0.80  thf('35', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.60/0.80           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['33', '34'])).
% 0.60/0.80  thf('36', plain,
% 0.60/0.80      (![X23 : $i, X24 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.60/0.80           = (k2_xboole_0 @ X23 @ X24))),
% 0.60/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.60/0.80  thf('37', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.80  thf('38', plain,
% 0.60/0.80      (![X23 : $i, X24 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.60/0.80           = (k2_xboole_0 @ X23 @ X24))),
% 0.60/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.60/0.80  thf('39', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.60/0.80           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['37', '38'])).
% 0.60/0.80  thf('40', plain,
% 0.60/0.80      (![X21 : $i, X22 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)) = (X21))),
% 0.60/0.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.60/0.80  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['39', '40'])).
% 0.60/0.80  thf('42', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['41', '42'])).
% 0.60/0.80  thf('44', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['36', '43'])).
% 0.60/0.80  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['41', '42'])).
% 0.60/0.80  thf('46', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.80      inference('demod', [status(thm)], ['44', '45'])).
% 0.60/0.80  thf('47', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.60/0.80      inference('demod', [status(thm)], ['35', '46'])).
% 0.60/0.80  thf('48', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.60/0.80           = (X1))),
% 0.60/0.80      inference('demod', [status(thm)], ['4', '47'])).
% 0.60/0.80  thf('49', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.60/0.80           (k4_xboole_0 @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['1', '48'])).
% 0.60/0.80  thf('50', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf('51', plain,
% 0.60/0.80      (![X21 : $i, X22 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)) = (X21))),
% 0.60/0.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.60/0.80  thf('52', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.60/0.80           = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.80      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.60/0.80  thf('53', plain,
% 0.60/0.80      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['0', '52'])).
% 0.60/0.80  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.60/0.80  
% 0.60/0.80  % SZS output end Refutation
% 0.60/0.80  
% 0.60/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
