%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J420Fc9i5N

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:11 EST 2020

% Result     : Theorem 4.10s
% Output     : Refutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   81 (  95 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  578 ( 686 expanded)
%              Number of equality atoms :   53 (  64 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
 != ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
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
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
 != ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X34 @ X35 ) @ X34 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_xboole_0 @ X32 @ X33 )
        = X32 )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_xboole_0 @ X14 @ X17 ) )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
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
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ X36 @ ( k4_xboole_0 @ X37 @ X36 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_xboole_0 @ X29 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('35',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('36',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X24: $i] :
      ( ( k2_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X38 @ X39 ) @ X40 )
      = ( k4_xboole_0 @ X38 @ ( k2_xboole_0 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

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
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B_1 )
 != ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J420Fc9i5N
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.10/4.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.10/4.39  % Solved by: fo/fo7.sh
% 4.10/4.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.10/4.39  % done 6506 iterations in 3.923s
% 4.10/4.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.10/4.39  % SZS output start Refutation
% 4.10/4.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.10/4.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.10/4.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.10/4.39  thf(sk_B_type, type, sk_B: $i > $i).
% 4.10/4.39  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.10/4.39  thf(sk_A_type, type, sk_A: $i).
% 4.10/4.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.10/4.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.10/4.39  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.10/4.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.10/4.39  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.10/4.39  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.10/4.39  thf(t47_xboole_1, conjecture,
% 4.10/4.39    (![A:$i,B:$i]:
% 4.10/4.39     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.10/4.39  thf(zf_stmt_0, negated_conjecture,
% 4.10/4.39    (~( ![A:$i,B:$i]:
% 4.10/4.39        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 4.10/4.39          ( k4_xboole_0 @ A @ B ) ) )),
% 4.10/4.39    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 4.10/4.39  thf('0', plain,
% 4.10/4.39      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B_1))
% 4.10/4.39         != (k4_xboole_0 @ sk_A @ sk_B_1))),
% 4.10/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.39  thf(commutativity_k3_xboole_0, axiom,
% 4.10/4.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.10/4.39  thf('1', plain,
% 4.10/4.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.10/4.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.10/4.39  thf('2', plain,
% 4.10/4.39      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 4.10/4.39         != (k4_xboole_0 @ sk_A @ sk_B_1))),
% 4.10/4.39      inference('demod', [status(thm)], ['0', '1'])).
% 4.10/4.39  thf(t36_xboole_1, axiom,
% 4.10/4.39    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.10/4.39  thf('3', plain,
% 4.10/4.39      (![X34 : $i, X35 : $i]: (r1_tarski @ (k4_xboole_0 @ X34 @ X35) @ X34)),
% 4.10/4.39      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.10/4.39  thf(t28_xboole_1, axiom,
% 4.10/4.39    (![A:$i,B:$i]:
% 4.10/4.39     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.10/4.39  thf('4', plain,
% 4.10/4.39      (![X32 : $i, X33 : $i]:
% 4.10/4.39         (((k3_xboole_0 @ X32 @ X33) = (X32)) | ~ (r1_tarski @ X32 @ X33))),
% 4.10/4.39      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.10/4.39  thf('5', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 4.10/4.39           = (k4_xboole_0 @ X0 @ X1))),
% 4.10/4.39      inference('sup-', [status(thm)], ['3', '4'])).
% 4.10/4.39  thf('6', plain,
% 4.10/4.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.10/4.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.10/4.39  thf('7', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.10/4.39           = (k4_xboole_0 @ X0 @ X1))),
% 4.10/4.39      inference('demod', [status(thm)], ['5', '6'])).
% 4.10/4.39  thf(t3_xboole_0, axiom,
% 4.10/4.39    (![A:$i,B:$i]:
% 4.10/4.39     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 4.10/4.39            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.10/4.39       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.10/4.39            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 4.10/4.39  thf('8', plain,
% 4.10/4.39      (![X10 : $i, X11 : $i]:
% 4.10/4.39         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X11))),
% 4.10/4.39      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.10/4.39  thf('9', plain,
% 4.10/4.39      (![X10 : $i, X11 : $i]:
% 4.10/4.39         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 4.10/4.39      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.10/4.39  thf(d5_xboole_0, axiom,
% 4.10/4.39    (![A:$i,B:$i,C:$i]:
% 4.10/4.39     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.10/4.39       ( ![D:$i]:
% 4.10/4.39         ( ( r2_hidden @ D @ C ) <=>
% 4.10/4.39           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.10/4.39  thf('10', plain,
% 4.10/4.39      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 4.10/4.39         (~ (r2_hidden @ X8 @ X7)
% 4.10/4.39          | ~ (r2_hidden @ X8 @ X6)
% 4.10/4.39          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 4.10/4.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.10/4.39  thf('11', plain,
% 4.10/4.39      (![X5 : $i, X6 : $i, X8 : $i]:
% 4.10/4.39         (~ (r2_hidden @ X8 @ X6)
% 4.10/4.39          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 4.10/4.39      inference('simplify', [status(thm)], ['10'])).
% 4.10/4.39  thf('12', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.10/4.39         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 4.10/4.39          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 4.10/4.39      inference('sup-', [status(thm)], ['9', '11'])).
% 4.10/4.39  thf('13', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 4.10/4.39          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 4.10/4.39      inference('sup-', [status(thm)], ['8', '12'])).
% 4.10/4.39  thf('14', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 4.10/4.39      inference('simplify', [status(thm)], ['13'])).
% 4.10/4.39  thf(t7_xboole_0, axiom,
% 4.10/4.39    (![A:$i]:
% 4.10/4.39     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.10/4.39          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 4.10/4.39  thf('15', plain,
% 4.10/4.39      (![X18 : $i]:
% 4.10/4.39         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 4.10/4.39      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.10/4.39  thf(t4_xboole_0, axiom,
% 4.10/4.39    (![A:$i,B:$i]:
% 4.10/4.39     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 4.10/4.39            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.10/4.39       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.10/4.39            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 4.10/4.39  thf('16', plain,
% 4.10/4.39      (![X14 : $i, X16 : $i, X17 : $i]:
% 4.10/4.39         (~ (r2_hidden @ X16 @ (k3_xboole_0 @ X14 @ X17))
% 4.10/4.39          | ~ (r1_xboole_0 @ X14 @ X17))),
% 4.10/4.39      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.10/4.39  thf('17', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 4.10/4.39      inference('sup-', [status(thm)], ['15', '16'])).
% 4.10/4.39  thf('18', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 4.10/4.39      inference('sup-', [status(thm)], ['14', '17'])).
% 4.10/4.39  thf('19', plain,
% 4.10/4.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.10/4.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.10/4.39  thf('20', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.10/4.39      inference('demod', [status(thm)], ['18', '19'])).
% 4.10/4.39  thf(t16_xboole_1, axiom,
% 4.10/4.39    (![A:$i,B:$i,C:$i]:
% 4.10/4.39     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 4.10/4.39       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 4.10/4.39  thf('21', plain,
% 4.10/4.39      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X23)
% 4.10/4.39           = (k3_xboole_0 @ X21 @ (k3_xboole_0 @ X22 @ X23)))),
% 4.10/4.39      inference('cnf', [status(esa)], [t16_xboole_1])).
% 4.10/4.39  thf('22', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.10/4.39         ((k1_xboole_0)
% 4.10/4.39           = (k3_xboole_0 @ X1 @ 
% 4.10/4.39              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))))),
% 4.10/4.39      inference('sup+', [status(thm)], ['20', '21'])).
% 4.10/4.39  thf('23', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((k1_xboole_0)
% 4.10/4.39           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 4.10/4.39      inference('sup+', [status(thm)], ['7', '22'])).
% 4.10/4.39  thf('24', plain,
% 4.10/4.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.10/4.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.10/4.39  thf(t39_xboole_1, axiom,
% 4.10/4.39    (![A:$i,B:$i]:
% 4.10/4.39     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.10/4.39  thf('25', plain,
% 4.10/4.39      (![X36 : $i, X37 : $i]:
% 4.10/4.39         ((k2_xboole_0 @ X36 @ (k4_xboole_0 @ X37 @ X36))
% 4.10/4.39           = (k2_xboole_0 @ X36 @ X37))),
% 4.10/4.39      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.10/4.39  thf('26', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.10/4.39           = (k4_xboole_0 @ X0 @ X1))),
% 4.10/4.39      inference('demod', [status(thm)], ['5', '6'])).
% 4.10/4.39  thf(t23_xboole_1, axiom,
% 4.10/4.39    (![A:$i,B:$i,C:$i]:
% 4.10/4.39     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 4.10/4.39       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 4.10/4.39  thf('27', plain,
% 4.10/4.39      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ X29 @ (k2_xboole_0 @ X30 @ X31))
% 4.10/4.39           = (k2_xboole_0 @ (k3_xboole_0 @ X29 @ X30) @ 
% 4.10/4.39              (k3_xboole_0 @ X29 @ X31)))),
% 4.10/4.39      inference('cnf', [status(esa)], [t23_xboole_1])).
% 4.10/4.39  thf('28', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 4.10/4.39           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 4.10/4.39      inference('sup+', [status(thm)], ['26', '27'])).
% 4.10/4.39  thf('29', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 4.10/4.39           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 4.10/4.39      inference('sup+', [status(thm)], ['25', '28'])).
% 4.10/4.39  thf(commutativity_k2_xboole_0, axiom,
% 4.10/4.39    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.10/4.39  thf('30', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.10/4.39      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.10/4.39  thf(t21_xboole_1, axiom,
% 4.10/4.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 4.10/4.39  thf('31', plain,
% 4.10/4.39      (![X25 : $i, X26 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (X25))),
% 4.10/4.39      inference('cnf', [status(esa)], [t21_xboole_1])).
% 4.10/4.39  thf('32', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 4.10/4.39      inference('sup+', [status(thm)], ['30', '31'])).
% 4.10/4.39  thf('33', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.10/4.39      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.10/4.39  thf('34', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((X0)
% 4.10/4.39           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 4.10/4.39      inference('demod', [status(thm)], ['29', '32', '33'])).
% 4.10/4.39  thf('35', plain,
% 4.10/4.39      (![X18 : $i]:
% 4.10/4.39         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 4.10/4.39      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.10/4.39  thf(t7_boole, axiom,
% 4.10/4.39    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 4.10/4.39  thf('36', plain,
% 4.10/4.39      (![X41 : $i, X42 : $i]:
% 4.10/4.39         (~ (r2_hidden @ X41 @ X42) | ~ (v1_xboole_0 @ X42))),
% 4.10/4.39      inference('cnf', [status(esa)], [t7_boole])).
% 4.10/4.39  thf('37', plain,
% 4.10/4.39      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.10/4.39      inference('sup-', [status(thm)], ['35', '36'])).
% 4.10/4.39  thf(t1_boole, axiom,
% 4.10/4.39    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.10/4.39  thf('38', plain, (![X24 : $i]: ((k2_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 4.10/4.39      inference('cnf', [status(esa)], [t1_boole])).
% 4.10/4.39  thf('39', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         (((k2_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 4.10/4.39      inference('sup+', [status(thm)], ['37', '38'])).
% 4.10/4.39  thf('40', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 4.10/4.39          | ~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1)))),
% 4.10/4.39      inference('sup+', [status(thm)], ['34', '39'])).
% 4.10/4.39  thf('41', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         (~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 4.10/4.39          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 4.10/4.39      inference('sup-', [status(thm)], ['24', '40'])).
% 4.10/4.39  thf('42', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         (~ (v1_xboole_0 @ k1_xboole_0)
% 4.10/4.39          | ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 4.10/4.39              = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 4.10/4.39                 X1)))),
% 4.10/4.39      inference('sup-', [status(thm)], ['23', '41'])).
% 4.10/4.39  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.10/4.39  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.10/4.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.10/4.39  thf(t41_xboole_1, axiom,
% 4.10/4.39    (![A:$i,B:$i,C:$i]:
% 4.10/4.39     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 4.10/4.39       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.10/4.39  thf('44', plain,
% 4.10/4.39      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.10/4.39         ((k4_xboole_0 @ (k4_xboole_0 @ X38 @ X39) @ X40)
% 4.10/4.39           = (k4_xboole_0 @ X38 @ (k2_xboole_0 @ X39 @ X40)))),
% 4.10/4.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.10/4.39  thf('45', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.10/4.39      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.10/4.39  thf(t22_xboole_1, axiom,
% 4.10/4.39    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 4.10/4.39  thf('46', plain,
% 4.10/4.39      (![X27 : $i, X28 : $i]:
% 4.10/4.39         ((k2_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28)) = (X27))),
% 4.10/4.39      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.10/4.39  thf('47', plain,
% 4.10/4.39      (![X0 : $i, X1 : $i]:
% 4.10/4.39         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 4.10/4.39           = (k4_xboole_0 @ X0 @ X1))),
% 4.10/4.39      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 4.10/4.39  thf('48', plain,
% 4.10/4.39      (((k4_xboole_0 @ sk_A @ sk_B_1) != (k4_xboole_0 @ sk_A @ sk_B_1))),
% 4.10/4.39      inference('demod', [status(thm)], ['2', '47'])).
% 4.10/4.39  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 4.10/4.39  
% 4.10/4.39  % SZS output end Refutation
% 4.10/4.39  
% 4.23/4.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
