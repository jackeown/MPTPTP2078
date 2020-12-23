%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AaQOBMObUY

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:10 EST 2020

% Result     : Theorem 42.44s
% Output     : Refutation 42.44s
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

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X14 ) @ X14 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k3_xboole_0 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
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
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X32 @ X33 ) @ X34 )
      = ( k4_xboole_0 @ X32 @ ( k2_xboole_0 @ X33 @ X34 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k3_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
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
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AaQOBMObUY
% 0.16/0.37  % Computer   : n008.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 09:27:30 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 42.44/42.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 42.44/42.72  % Solved by: fo/fo7.sh
% 42.44/42.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 42.44/42.72  % done 14868 iterations in 42.236s
% 42.44/42.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 42.44/42.72  % SZS output start Refutation
% 42.44/42.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 42.44/42.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 42.44/42.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 42.44/42.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 42.44/42.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 42.44/42.72  thf(sk_B_type, type, sk_B: $i).
% 42.44/42.72  thf(sk_A_type, type, sk_A: $i).
% 42.44/42.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 42.44/42.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 42.44/42.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 42.44/42.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 42.44/42.72  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 42.44/42.72  thf(t47_xboole_1, conjecture,
% 42.44/42.72    (![A:$i,B:$i]:
% 42.44/42.72     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 42.44/42.72  thf(zf_stmt_0, negated_conjecture,
% 42.44/42.72    (~( ![A:$i,B:$i]:
% 42.44/42.72        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 42.44/42.72          ( k4_xboole_0 @ A @ B ) ) )),
% 42.44/42.72    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 42.44/42.72  thf('0', plain,
% 42.44/42.72      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 42.44/42.72         != (k4_xboole_0 @ sk_A @ sk_B))),
% 42.44/42.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.44/42.72  thf(commutativity_k3_xboole_0, axiom,
% 42.44/42.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 42.44/42.72  thf('1', plain,
% 42.44/42.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.44/42.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.44/42.72  thf('2', plain,
% 42.44/42.72      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 42.44/42.72         != (k4_xboole_0 @ sk_A @ sk_B))),
% 42.44/42.72      inference('demod', [status(thm)], ['0', '1'])).
% 42.44/42.72  thf(t36_xboole_1, axiom,
% 42.44/42.72    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 42.44/42.72  thf('3', plain,
% 42.44/42.72      (![X30 : $i, X31 : $i]: (r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X30)),
% 42.44/42.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 42.44/42.72  thf(t28_xboole_1, axiom,
% 42.44/42.72    (![A:$i,B:$i]:
% 42.44/42.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 42.44/42.72  thf('4', plain,
% 42.44/42.72      (![X27 : $i, X28 : $i]:
% 42.44/42.72         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 42.44/42.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 42.44/42.72  thf('5', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 42.44/42.72           = (k4_xboole_0 @ X0 @ X1))),
% 42.44/42.72      inference('sup-', [status(thm)], ['3', '4'])).
% 42.44/42.72  thf('6', plain,
% 42.44/42.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.44/42.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.44/42.72  thf('7', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 42.44/42.72           = (k4_xboole_0 @ X0 @ X1))),
% 42.44/42.72      inference('demod', [status(thm)], ['5', '6'])).
% 42.44/42.72  thf(t3_xboole_0, axiom,
% 42.44/42.72    (![A:$i,B:$i]:
% 42.44/42.72     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 42.44/42.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 42.44/42.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 42.44/42.72            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 42.44/42.72  thf('8', plain,
% 42.44/42.72      (![X14 : $i, X15 : $i]:
% 42.44/42.72         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C @ X15 @ X14) @ X15))),
% 42.44/42.72      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.44/42.72  thf('9', plain,
% 42.44/42.72      (![X14 : $i, X15 : $i]:
% 42.44/42.72         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C @ X15 @ X14) @ X14))),
% 42.44/42.72      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.44/42.72  thf(d5_xboole_0, axiom,
% 42.44/42.72    (![A:$i,B:$i,C:$i]:
% 42.44/42.72     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 42.44/42.72       ( ![D:$i]:
% 42.44/42.72         ( ( r2_hidden @ D @ C ) <=>
% 42.44/42.72           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 42.44/42.72  thf('10', plain,
% 42.44/42.72      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 42.44/42.72         (~ (r2_hidden @ X8 @ X7)
% 42.44/42.72          | ~ (r2_hidden @ X8 @ X6)
% 42.44/42.72          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 42.44/42.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 42.44/42.72  thf('11', plain,
% 42.44/42.72      (![X5 : $i, X6 : $i, X8 : $i]:
% 42.44/42.72         (~ (r2_hidden @ X8 @ X6)
% 42.44/42.72          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 42.44/42.72      inference('simplify', [status(thm)], ['10'])).
% 42.44/42.72  thf('12', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.44/42.72         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 42.44/42.72          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 42.44/42.72      inference('sup-', [status(thm)], ['9', '11'])).
% 42.44/42.72  thf('13', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 42.44/42.72          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 42.44/42.72      inference('sup-', [status(thm)], ['8', '12'])).
% 42.44/42.72  thf('14', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 42.44/42.72      inference('simplify', [status(thm)], ['13'])).
% 42.44/42.72  thf(d7_xboole_0, axiom,
% 42.44/42.72    (![A:$i,B:$i]:
% 42.44/42.72     ( ( r1_xboole_0 @ A @ B ) <=>
% 42.44/42.72       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 42.44/42.72  thf('15', plain,
% 42.44/42.72      (![X10 : $i, X11 : $i]:
% 42.44/42.72         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 42.44/42.72          | ~ (r1_xboole_0 @ X10 @ X11))),
% 42.44/42.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 42.44/42.72  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 42.44/42.72  thf('16', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 42.44/42.72      inference('cnf', [status(esa)], [d2_xboole_0])).
% 42.44/42.72  thf('17', plain,
% 42.44/42.72      (![X10 : $i, X11 : $i]:
% 42.44/42.72         (((k3_xboole_0 @ X10 @ X11) = (o_0_0_xboole_0))
% 42.44/42.72          | ~ (r1_xboole_0 @ X10 @ X11))),
% 42.44/42.72      inference('demod', [status(thm)], ['15', '16'])).
% 42.44/42.72  thf('18', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (o_0_0_xboole_0))),
% 42.44/42.72      inference('sup-', [status(thm)], ['14', '17'])).
% 42.44/42.72  thf('19', plain,
% 42.44/42.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.44/42.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.44/42.72  thf('20', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 42.44/42.72      inference('demod', [status(thm)], ['18', '19'])).
% 42.44/42.72  thf(t16_xboole_1, axiom,
% 42.44/42.72    (![A:$i,B:$i,C:$i]:
% 42.44/42.72     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 42.44/42.72       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 42.44/42.72  thf('21', plain,
% 42.44/42.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 42.44/42.72         ((k3_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X23)
% 42.44/42.72           = (k3_xboole_0 @ X21 @ (k3_xboole_0 @ X22 @ X23)))),
% 42.44/42.72      inference('cnf', [status(esa)], [t16_xboole_1])).
% 42.44/42.72  thf('22', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.44/42.72         ((o_0_0_xboole_0)
% 42.44/42.72           = (k3_xboole_0 @ X1 @ 
% 42.44/42.72              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))))),
% 42.44/42.72      inference('sup+', [status(thm)], ['20', '21'])).
% 42.44/42.72  thf('23', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((o_0_0_xboole_0)
% 42.44/42.72           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 42.44/42.72      inference('sup+', [status(thm)], ['7', '22'])).
% 42.44/42.72  thf('24', plain,
% 42.44/42.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.44/42.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.44/42.72  thf('25', plain,
% 42.44/42.72      (![X10 : $i, X12 : $i]:
% 42.44/42.72         ((r1_xboole_0 @ X10 @ X12)
% 42.44/42.72          | ((k3_xboole_0 @ X10 @ X12) != (k1_xboole_0)))),
% 42.44/42.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 42.44/42.72  thf('26', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 42.44/42.72      inference('cnf', [status(esa)], [d2_xboole_0])).
% 42.44/42.72  thf('27', plain,
% 42.44/42.72      (![X10 : $i, X12 : $i]:
% 42.44/42.72         ((r1_xboole_0 @ X10 @ X12)
% 42.44/42.72          | ((k3_xboole_0 @ X10 @ X12) != (o_0_0_xboole_0)))),
% 42.44/42.72      inference('demod', [status(thm)], ['25', '26'])).
% 42.44/42.72  thf('28', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         (((k3_xboole_0 @ X1 @ X0) != (o_0_0_xboole_0))
% 42.44/42.72          | (r1_xboole_0 @ X0 @ X1))),
% 42.44/42.72      inference('sup-', [status(thm)], ['24', '27'])).
% 42.44/42.72  thf('29', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 42.44/42.72          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 42.44/42.72      inference('sup-', [status(thm)], ['23', '28'])).
% 42.44/42.72  thf('30', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X1)),
% 42.44/42.72      inference('simplify', [status(thm)], ['29'])).
% 42.44/42.72  thf('31', plain,
% 42.44/42.72      (![X5 : $i, X6 : $i, X9 : $i]:
% 42.44/42.72         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 42.44/42.72          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 42.44/42.72          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 42.44/42.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 42.44/42.72  thf('32', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 42.44/42.72          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 42.44/42.72      inference('eq_fact', [status(thm)], ['31'])).
% 42.44/42.72  thf('33', plain,
% 42.44/42.72      (![X5 : $i, X6 : $i, X9 : $i]:
% 42.44/42.72         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 42.44/42.72          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 42.44/42.72          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 42.44/42.72          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 42.44/42.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 42.44/42.72  thf('34', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 42.44/42.72          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 42.44/42.72          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 42.44/42.72          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 42.44/42.72      inference('sup-', [status(thm)], ['32', '33'])).
% 42.44/42.72  thf('35', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 42.44/42.72          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 42.44/42.72          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 42.44/42.72      inference('simplify', [status(thm)], ['34'])).
% 42.44/42.72  thf('36', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 42.44/42.72          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 42.44/42.72      inference('eq_fact', [status(thm)], ['31'])).
% 42.44/42.72  thf('37', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 42.44/42.72          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 42.44/42.72      inference('clc', [status(thm)], ['35', '36'])).
% 42.44/42.72  thf('38', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 42.44/42.72          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 42.44/42.72      inference('eq_fact', [status(thm)], ['31'])).
% 42.44/42.72  thf('39', plain,
% 42.44/42.72      (![X14 : $i, X16 : $i, X17 : $i]:
% 42.44/42.72         (~ (r2_hidden @ X16 @ X14)
% 42.44/42.72          | ~ (r2_hidden @ X16 @ X17)
% 42.44/42.72          | ~ (r1_xboole_0 @ X14 @ X17))),
% 42.44/42.72      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.44/42.72  thf('40', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.44/42.72         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 42.44/42.72          | ~ (r1_xboole_0 @ X0 @ X2)
% 42.44/42.72          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2))),
% 42.44/42.72      inference('sup-', [status(thm)], ['38', '39'])).
% 42.44/42.72  thf('41', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         (((X1) = (k4_xboole_0 @ X1 @ X0))
% 42.44/42.72          | ~ (r1_xboole_0 @ X1 @ X0)
% 42.44/42.72          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 42.44/42.72      inference('sup-', [status(thm)], ['37', '40'])).
% 42.44/42.72  thf('42', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         (~ (r1_xboole_0 @ X1 @ X0) | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 42.44/42.72      inference('simplify', [status(thm)], ['41'])).
% 42.44/42.72  thf('43', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 42.44/42.72           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 42.44/42.72      inference('sup-', [status(thm)], ['30', '42'])).
% 42.44/42.72  thf(t41_xboole_1, axiom,
% 42.44/42.72    (![A:$i,B:$i,C:$i]:
% 42.44/42.72     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 42.44/42.72       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 42.44/42.72  thf('44', plain,
% 42.44/42.72      (![X32 : $i, X33 : $i, X34 : $i]:
% 42.44/42.72         ((k4_xboole_0 @ (k4_xboole_0 @ X32 @ X33) @ X34)
% 42.44/42.72           = (k4_xboole_0 @ X32 @ (k2_xboole_0 @ X33 @ X34)))),
% 42.44/42.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 42.44/42.72  thf(commutativity_k2_xboole_0, axiom,
% 42.44/42.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 42.44/42.72  thf('45', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 42.44/42.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 42.44/42.72  thf(t22_xboole_1, axiom,
% 42.44/42.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 42.44/42.72  thf('46', plain,
% 42.44/42.72      (![X25 : $i, X26 : $i]:
% 42.44/42.72         ((k2_xboole_0 @ X25 @ (k3_xboole_0 @ X25 @ X26)) = (X25))),
% 42.44/42.72      inference('cnf', [status(esa)], [t22_xboole_1])).
% 42.44/42.72  thf('47', plain,
% 42.44/42.72      (![X0 : $i, X1 : $i]:
% 42.44/42.72         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 42.44/42.72           = (k4_xboole_0 @ X1 @ X0))),
% 42.44/42.72      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 42.44/42.72  thf('48', plain,
% 42.44/42.72      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 42.44/42.72      inference('demod', [status(thm)], ['2', '47'])).
% 42.44/42.72  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 42.44/42.72  
% 42.44/42.72  % SZS output end Refutation
% 42.44/42.72  
% 42.44/42.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
