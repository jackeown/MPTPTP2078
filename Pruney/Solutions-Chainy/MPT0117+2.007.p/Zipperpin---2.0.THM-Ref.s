%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N0kvlO0V1d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:47 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 100 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  521 ( 703 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('3',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ X52 @ X53 )
      | ~ ( r1_tarski @ X54 @ X53 )
      | ( r1_tarski @ ( k2_xboole_0 @ X52 @ X54 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X39: $i,X40: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X39 @ X40 ) @ X39 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_xboole_0 @ X34 @ X35 )
        = X34 )
      | ~ ( r1_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','24'])).

thf('26',plain,(
    ! [X39: $i,X40: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X39 @ X40 ) @ X39 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('31',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ ( k3_xboole_0 @ X32 @ X33 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ X22 @ X21 )
        = X21 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ ( k3_xboole_0 @ X32 @ X33 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X51: $i] :
      ( ( k5_xboole_0 @ X51 @ k1_xboole_0 )
      = X51 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X39: $i,X40: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X39 @ X40 ) @ X39 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('48',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X31 )
      | ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['5','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N0kvlO0V1d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:58:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.57/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.85  % Solved by: fo/fo7.sh
% 0.57/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.85  % done 950 iterations in 0.383s
% 0.57/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.85  % SZS output start Refutation
% 0.57/0.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.57/0.85  thf(sk_B_type, type, sk_B: $i > $i).
% 0.57/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.85  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.57/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.57/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.85  thf(t110_xboole_1, conjecture,
% 0.57/0.85    (![A:$i,B:$i,C:$i]:
% 0.57/0.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.57/0.85       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.57/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.57/0.85        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.57/0.85          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 0.57/0.85    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 0.57/0.85  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B_1)),
% 0.57/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.85  thf('1', plain, ((r1_tarski @ sk_C @ sk_B_1)),
% 0.57/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.85  thf('2', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.57/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.85  thf(t8_xboole_1, axiom,
% 0.57/0.85    (![A:$i,B:$i,C:$i]:
% 0.57/0.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.57/0.85       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.57/0.85  thf('3', plain,
% 0.57/0.85      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.57/0.85         (~ (r1_tarski @ X52 @ X53)
% 0.57/0.85          | ~ (r1_tarski @ X54 @ X53)
% 0.57/0.85          | (r1_tarski @ (k2_xboole_0 @ X52 @ X54) @ X53))),
% 0.57/0.85      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.57/0.85  thf('4', plain,
% 0.57/0.85      (![X0 : $i]:
% 0.57/0.85         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.57/0.85          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.57/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.57/0.85  thf('5', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B_1)),
% 0.57/0.85      inference('sup-', [status(thm)], ['1', '4'])).
% 0.57/0.85  thf(t7_xboole_0, axiom,
% 0.57/0.85    (![A:$i]:
% 0.57/0.85     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.57/0.85          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.57/0.85  thf('6', plain,
% 0.57/0.85      (![X14 : $i]:
% 0.57/0.85         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.57/0.85      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.85  thf(t36_xboole_1, axiom,
% 0.57/0.85    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.57/0.85  thf('7', plain,
% 0.57/0.85      (![X39 : $i, X40 : $i]: (r1_tarski @ (k4_xboole_0 @ X39 @ X40) @ X39)),
% 0.57/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.57/0.85  thf(t28_xboole_1, axiom,
% 0.57/0.85    (![A:$i,B:$i]:
% 0.57/0.85     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.57/0.85  thf('8', plain,
% 0.57/0.85      (![X34 : $i, X35 : $i]:
% 0.57/0.85         (((k3_xboole_0 @ X34 @ X35) = (X34)) | ~ (r1_tarski @ X34 @ X35))),
% 0.57/0.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.85  thf('9', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i]:
% 0.57/0.85         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.57/0.85           = (k4_xboole_0 @ X0 @ X1))),
% 0.57/0.85      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.85  thf(commutativity_k3_xboole_0, axiom,
% 0.57/0.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.57/0.85  thf('10', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.85  thf('11', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i]:
% 0.57/0.85         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.57/0.85           = (k4_xboole_0 @ X0 @ X1))),
% 0.57/0.85      inference('demod', [status(thm)], ['9', '10'])).
% 0.57/0.85  thf('12', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.85  thf(t100_xboole_1, axiom,
% 0.57/0.85    (![A:$i,B:$i]:
% 0.57/0.85     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.57/0.85  thf('13', plain,
% 0.57/0.85      (![X15 : $i, X16 : $i]:
% 0.57/0.85         ((k4_xboole_0 @ X15 @ X16)
% 0.57/0.85           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.57/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.85  thf(t1_xboole_0, axiom,
% 0.57/0.85    (![A:$i,B:$i,C:$i]:
% 0.57/0.85     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.57/0.85       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.57/0.85  thf('14', plain,
% 0.57/0.85      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.57/0.85         (~ (r2_hidden @ X10 @ X11)
% 0.57/0.85          | ~ (r2_hidden @ X10 @ X12)
% 0.57/0.85          | ~ (r2_hidden @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.57/0.85      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.57/0.85  thf('15', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.85         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.57/0.85          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.57/0.85          | ~ (r2_hidden @ X2 @ X1))),
% 0.57/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.57/0.85  thf(d4_xboole_0, axiom,
% 0.57/0.85    (![A:$i,B:$i,C:$i]:
% 0.57/0.85     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.57/0.85       ( ![D:$i]:
% 0.57/0.85         ( ( r2_hidden @ D @ C ) <=>
% 0.57/0.85           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.57/0.85  thf('16', plain,
% 0.57/0.85      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.57/0.85         (~ (r2_hidden @ X8 @ X7)
% 0.57/0.85          | (r2_hidden @ X8 @ X5)
% 0.57/0.85          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.57/0.85      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.57/0.85  thf('17', plain,
% 0.57/0.85      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.57/0.85         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.57/0.85      inference('simplify', [status(thm)], ['16'])).
% 0.57/0.85  thf('18', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.85         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.57/0.85          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.85      inference('clc', [status(thm)], ['15', '17'])).
% 0.57/0.85  thf('19', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.85         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.57/0.85          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.57/0.85      inference('sup-', [status(thm)], ['12', '18'])).
% 0.57/0.85  thf('20', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.85         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.57/0.85          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 0.57/0.85      inference('sup-', [status(thm)], ['11', '19'])).
% 0.57/0.85  thf('21', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i]:
% 0.57/0.85         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.57/0.85           = (k4_xboole_0 @ X0 @ X1))),
% 0.57/0.85      inference('demod', [status(thm)], ['9', '10'])).
% 0.57/0.85  thf('22', plain,
% 0.57/0.85      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.57/0.85         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.57/0.85      inference('simplify', [status(thm)], ['16'])).
% 0.57/0.85  thf('23', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.85         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.57/0.85      inference('sup-', [status(thm)], ['21', '22'])).
% 0.57/0.85  thf('24', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.85         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.57/0.85      inference('clc', [status(thm)], ['20', '23'])).
% 0.57/0.85  thf('25', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i]:
% 0.57/0.85         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.57/0.85      inference('sup-', [status(thm)], ['6', '24'])).
% 0.57/0.85  thf('26', plain,
% 0.57/0.85      (![X39 : $i, X40 : $i]: (r1_tarski @ (k4_xboole_0 @ X39 @ X40) @ X39)),
% 0.57/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.57/0.85  thf('27', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i]: (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.57/0.85      inference('sup+', [status(thm)], ['25', '26'])).
% 0.57/0.85  thf('28', plain,
% 0.57/0.85      (![X15 : $i, X16 : $i]:
% 0.57/0.85         ((k4_xboole_0 @ X15 @ X16)
% 0.57/0.85           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.57/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.85  thf(t107_xboole_1, axiom,
% 0.57/0.85    (![A:$i,B:$i,C:$i]:
% 0.57/0.85     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.57/0.85       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.57/0.85         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.57/0.85  thf('29', plain,
% 0.57/0.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.57/0.85         ((r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.57/0.85          | ~ (r1_tarski @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.57/0.85      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.57/0.85  thf('30', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.85         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.57/0.85          | (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.57/0.85      inference('sup-', [status(thm)], ['28', '29'])).
% 0.57/0.85  thf(t22_xboole_1, axiom,
% 0.57/0.85    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.57/0.85  thf('31', plain,
% 0.57/0.85      (![X32 : $i, X33 : $i]:
% 0.57/0.85         ((k2_xboole_0 @ X32 @ (k3_xboole_0 @ X32 @ X33)) = (X32))),
% 0.57/0.85      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.57/0.85  thf('32', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.85         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 0.57/0.85      inference('demod', [status(thm)], ['30', '31'])).
% 0.57/0.85  thf('33', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.57/0.85      inference('sup-', [status(thm)], ['27', '32'])).
% 0.57/0.85  thf(t12_xboole_1, axiom,
% 0.57/0.85    (![A:$i,B:$i]:
% 0.57/0.85     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.57/0.85  thf('34', plain,
% 0.57/0.85      (![X21 : $i, X22 : $i]:
% 0.57/0.85         (((k2_xboole_0 @ X22 @ X21) = (X21)) | ~ (r1_tarski @ X22 @ X21))),
% 0.57/0.85      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.57/0.85  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.85      inference('sup-', [status(thm)], ['33', '34'])).
% 0.57/0.85  thf('36', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.85  thf('37', plain,
% 0.57/0.85      (![X32 : $i, X33 : $i]:
% 0.57/0.85         ((k2_xboole_0 @ X32 @ (k3_xboole_0 @ X32 @ X33)) = (X32))),
% 0.57/0.85      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.57/0.85  thf('38', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i]:
% 0.57/0.85         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.57/0.85      inference('sup+', [status(thm)], ['36', '37'])).
% 0.57/0.85  thf('39', plain,
% 0.57/0.85      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.85      inference('sup+', [status(thm)], ['35', '38'])).
% 0.57/0.85  thf('40', plain,
% 0.57/0.85      (![X15 : $i, X16 : $i]:
% 0.57/0.85         ((k4_xboole_0 @ X15 @ X16)
% 0.57/0.85           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.57/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.85  thf('41', plain,
% 0.57/0.85      (![X0 : $i]:
% 0.57/0.85         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.85      inference('sup+', [status(thm)], ['39', '40'])).
% 0.57/0.85  thf(t5_boole, axiom,
% 0.57/0.85    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.85  thf('42', plain, (![X51 : $i]: ((k5_xboole_0 @ X51 @ k1_xboole_0) = (X51))),
% 0.57/0.85      inference('cnf', [status(esa)], [t5_boole])).
% 0.57/0.85  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.57/0.85      inference('sup+', [status(thm)], ['41', '42'])).
% 0.57/0.85  thf('44', plain,
% 0.57/0.85      (![X39 : $i, X40 : $i]: (r1_tarski @ (k4_xboole_0 @ X39 @ X40) @ X39)),
% 0.57/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.57/0.85  thf('45', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.57/0.85      inference('sup+', [status(thm)], ['43', '44'])).
% 0.57/0.85  thf('46', plain,
% 0.57/0.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.57/0.85         ((r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.57/0.85          | ~ (r1_tarski @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.57/0.85      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.57/0.85  thf('47', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i]:
% 0.57/0.85         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 0.57/0.85      inference('sup-', [status(thm)], ['45', '46'])).
% 0.57/0.85  thf(t1_xboole_1, axiom,
% 0.57/0.85    (![A:$i,B:$i,C:$i]:
% 0.57/0.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.57/0.85       ( r1_tarski @ A @ C ) ))).
% 0.57/0.85  thf('48', plain,
% 0.57/0.85      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.57/0.85         (~ (r1_tarski @ X29 @ X30)
% 0.57/0.85          | ~ (r1_tarski @ X30 @ X31)
% 0.57/0.85          | (r1_tarski @ X29 @ X31))),
% 0.57/0.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.57/0.85  thf('49', plain,
% 0.57/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.85         ((r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.57/0.85          | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.57/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.57/0.85  thf('50', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B_1)),
% 0.57/0.85      inference('sup-', [status(thm)], ['5', '49'])).
% 0.57/0.85  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.57/0.85  
% 0.57/0.85  % SZS output end Refutation
% 0.57/0.85  
% 0.57/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
