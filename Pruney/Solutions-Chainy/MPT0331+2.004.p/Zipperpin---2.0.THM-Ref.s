%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6ZvvC5bFQM

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:04 EST 2020

% Result     : Theorem 4.12s
% Output     : Refutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 231 expanded)
%              Number of leaves         :   21 (  82 expanded)
%              Depth                    :   20
%              Number of atoms          :  599 (1920 expanded)
%              Number of equality atoms :   57 ( 156 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X34 @ X36 ) @ X37 )
        = ( k2_tarski @ X34 @ X36 ) )
      | ( r2_hidden @ X36 @ X37 )
      | ( r2_hidden @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','26','27','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('43',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','47'])).

thf('49',plain,(
    sk_C_1
 != ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6ZvvC5bFQM
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:37:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.12/4.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.12/4.33  % Solved by: fo/fo7.sh
% 4.12/4.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.12/4.33  % done 5940 iterations in 3.874s
% 4.12/4.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.12/4.33  % SZS output start Refutation
% 4.12/4.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.12/4.33  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.12/4.33  thf(sk_B_type, type, sk_B: $i).
% 4.12/4.33  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.12/4.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.12/4.33  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.12/4.33  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.12/4.33  thf(sk_A_type, type, sk_A: $i).
% 4.12/4.33  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.12/4.33  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.12/4.33  thf(t144_zfmisc_1, conjecture,
% 4.12/4.33    (![A:$i,B:$i,C:$i]:
% 4.12/4.33     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 4.12/4.33          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 4.12/4.33  thf(zf_stmt_0, negated_conjecture,
% 4.12/4.33    (~( ![A:$i,B:$i,C:$i]:
% 4.12/4.33        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 4.12/4.33             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 4.12/4.33    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 4.12/4.33  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C_1)),
% 4.12/4.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.33  thf(t72_zfmisc_1, axiom,
% 4.12/4.33    (![A:$i,B:$i,C:$i]:
% 4.12/4.33     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 4.12/4.33       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 4.12/4.33  thf('1', plain,
% 4.12/4.33      (![X34 : $i, X36 : $i, X37 : $i]:
% 4.12/4.33         (((k4_xboole_0 @ (k2_tarski @ X34 @ X36) @ X37)
% 4.12/4.33            = (k2_tarski @ X34 @ X36))
% 4.12/4.33          | (r2_hidden @ X36 @ X37)
% 4.12/4.33          | (r2_hidden @ X34 @ X37))),
% 4.12/4.33      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 4.12/4.33  thf(l36_xboole_1, axiom,
% 4.12/4.33    (![A:$i,B:$i,C:$i]:
% 4.12/4.33     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 4.12/4.33       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 4.12/4.33  thf('2', plain,
% 4.12/4.33      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 4.12/4.33           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X8)))),
% 4.12/4.33      inference('cnf', [status(esa)], [l36_xboole_1])).
% 4.12/4.33  thf(d3_tarski, axiom,
% 4.12/4.33    (![A:$i,B:$i]:
% 4.12/4.33     ( ( r1_tarski @ A @ B ) <=>
% 4.12/4.33       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.12/4.33  thf('3', plain,
% 4.12/4.33      (![X3 : $i, X5 : $i]:
% 4.12/4.33         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 4.12/4.33      inference('cnf', [status(esa)], [d3_tarski])).
% 4.12/4.33  thf('4', plain,
% 4.12/4.33      (![X3 : $i, X5 : $i]:
% 4.12/4.33         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 4.12/4.33      inference('cnf', [status(esa)], [d3_tarski])).
% 4.12/4.33  thf('5', plain,
% 4.12/4.33      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 4.12/4.33      inference('sup-', [status(thm)], ['3', '4'])).
% 4.12/4.33  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 4.12/4.33      inference('simplify', [status(thm)], ['5'])).
% 4.12/4.33  thf(t12_xboole_1, axiom,
% 4.12/4.33    (![A:$i,B:$i]:
% 4.12/4.33     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 4.12/4.33  thf('7', plain,
% 4.12/4.33      (![X9 : $i, X10 : $i]:
% 4.12/4.33         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 4.12/4.33      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.12/4.33  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 4.12/4.33      inference('sup-', [status(thm)], ['6', '7'])).
% 4.12/4.33  thf('9', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 4.12/4.33           = (k4_xboole_0 @ X1 @ X0))),
% 4.12/4.33      inference('sup+', [status(thm)], ['2', '8'])).
% 4.12/4.33  thf(t48_xboole_1, axiom,
% 4.12/4.33    (![A:$i,B:$i]:
% 4.12/4.33     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.12/4.33  thf('10', plain,
% 4.12/4.33      (![X18 : $i, X19 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 4.12/4.33           = (k3_xboole_0 @ X18 @ X19))),
% 4.12/4.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.12/4.33  thf('11', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 4.12/4.33           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)))),
% 4.12/4.33      inference('sup+', [status(thm)], ['9', '10'])).
% 4.12/4.33  thf('12', plain,
% 4.12/4.33      (![X18 : $i, X19 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 4.12/4.33           = (k3_xboole_0 @ X18 @ X19))),
% 4.12/4.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.12/4.33  thf('13', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k3_xboole_0 @ X1 @ X0)
% 4.12/4.33           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)))),
% 4.12/4.33      inference('demod', [status(thm)], ['11', '12'])).
% 4.12/4.33  thf('14', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 4.12/4.33           = (k4_xboole_0 @ X1 @ X0))),
% 4.12/4.33      inference('sup+', [status(thm)], ['2', '8'])).
% 4.12/4.33  thf('15', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0))
% 4.12/4.33           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)))),
% 4.12/4.33      inference('sup+', [status(thm)], ['13', '14'])).
% 4.12/4.33  thf('16', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 4.12/4.33           = (k4_xboole_0 @ X1 @ X0))),
% 4.12/4.33      inference('sup+', [status(thm)], ['2', '8'])).
% 4.12/4.33  thf('17', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0))
% 4.12/4.33           = (k4_xboole_0 @ X1 @ X0))),
% 4.12/4.33      inference('demod', [status(thm)], ['15', '16'])).
% 4.12/4.33  thf('18', plain,
% 4.12/4.33      (![X18 : $i, X19 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 4.12/4.33           = (k3_xboole_0 @ X18 @ X19))),
% 4.12/4.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.12/4.33  thf('19', plain,
% 4.12/4.33      (![X18 : $i, X19 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 4.12/4.33           = (k3_xboole_0 @ X18 @ X19))),
% 4.12/4.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.12/4.33  thf('20', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.12/4.33           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.12/4.33      inference('sup+', [status(thm)], ['18', '19'])).
% 4.12/4.33  thf(t22_xboole_1, axiom,
% 4.12/4.33    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 4.12/4.33  thf('21', plain,
% 4.12/4.33      (![X11 : $i, X12 : $i]:
% 4.12/4.33         ((k2_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)) = (X11))),
% 4.12/4.33      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.12/4.33  thf('22', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 4.12/4.33           = (X1))),
% 4.12/4.33      inference('sup+', [status(thm)], ['20', '21'])).
% 4.12/4.33  thf('23', plain,
% 4.12/4.33      (![X0 : $i]:
% 4.12/4.33         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ 
% 4.12/4.33           (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0))
% 4.12/4.33           = (k3_xboole_0 @ X0 @ X0))),
% 4.12/4.33      inference('sup+', [status(thm)], ['17', '22'])).
% 4.12/4.33  thf('24', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.12/4.33           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.12/4.33      inference('sup+', [status(thm)], ['18', '19'])).
% 4.12/4.33  thf(t49_xboole_1, axiom,
% 4.12/4.33    (![A:$i,B:$i,C:$i]:
% 4.12/4.33     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 4.12/4.33       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 4.12/4.33  thf('25', plain,
% 4.12/4.33      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.12/4.33         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 4.12/4.33           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 4.12/4.33      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.12/4.33  thf('26', plain,
% 4.12/4.33      (![X0 : $i, X1 : $i]:
% 4.12/4.33         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.12/4.34           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X1) @ X0))),
% 4.12/4.34      inference('demod', [status(thm)], ['24', '25'])).
% 4.12/4.34  thf('27', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i]:
% 4.12/4.34         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 4.12/4.34           = (k4_xboole_0 @ X1 @ X0))),
% 4.12/4.34      inference('sup+', [status(thm)], ['2', '8'])).
% 4.12/4.34  thf('28', plain,
% 4.12/4.34      (![X18 : $i, X19 : $i]:
% 4.12/4.34         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 4.12/4.34           = (k3_xboole_0 @ X18 @ X19))),
% 4.12/4.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.12/4.34  thf(t39_xboole_1, axiom,
% 4.12/4.34    (![A:$i,B:$i]:
% 4.12/4.34     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.12/4.34  thf('29', plain,
% 4.12/4.34      (![X13 : $i, X14 : $i]:
% 4.12/4.34         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 4.12/4.34           = (k2_xboole_0 @ X13 @ X14))),
% 4.12/4.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.12/4.34  thf('30', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i]:
% 4.12/4.34         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 4.12/4.34           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 4.12/4.34      inference('sup+', [status(thm)], ['28', '29'])).
% 4.12/4.34  thf(commutativity_k2_xboole_0, axiom,
% 4.12/4.34    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.12/4.34  thf('31', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.12/4.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.12/4.34  thf('32', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.12/4.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.12/4.34  thf('33', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i]:
% 4.12/4.34         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 4.12/4.34           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.12/4.34      inference('demod', [status(thm)], ['30', '31', '32'])).
% 4.12/4.34  thf('34', plain,
% 4.12/4.34      (![X13 : $i, X14 : $i]:
% 4.12/4.34         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 4.12/4.34           = (k2_xboole_0 @ X13 @ X14))),
% 4.12/4.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.12/4.34  thf('35', plain,
% 4.12/4.34      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.12/4.34      inference('demod', [status(thm)], ['23', '26', '27', '33', '34'])).
% 4.12/4.34  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 4.12/4.34      inference('sup-', [status(thm)], ['6', '7'])).
% 4.12/4.34  thf('37', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 4.12/4.34      inference('sup+', [status(thm)], ['35', '36'])).
% 4.12/4.34  thf(t52_xboole_1, axiom,
% 4.12/4.34    (![A:$i,B:$i,C:$i]:
% 4.12/4.34     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 4.12/4.34       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 4.12/4.34  thf('38', plain,
% 4.12/4.34      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.12/4.34         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 4.12/4.34           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 4.12/4.34              (k3_xboole_0 @ X23 @ X25)))),
% 4.12/4.34      inference('cnf', [status(esa)], [t52_xboole_1])).
% 4.12/4.34  thf('39', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i]:
% 4.12/4.34         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.12/4.34           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 4.12/4.34      inference('sup+', [status(thm)], ['37', '38'])).
% 4.12/4.34  thf('40', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.12/4.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.12/4.34  thf('41', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i]:
% 4.12/4.34         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.12/4.34           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 4.12/4.34      inference('demod', [status(thm)], ['39', '40'])).
% 4.12/4.34  thf('42', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 4.12/4.34      inference('sup+', [status(thm)], ['35', '36'])).
% 4.12/4.34  thf('43', plain,
% 4.12/4.34      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.12/4.34         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 4.12/4.34           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 4.12/4.34      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.12/4.34  thf('44', plain,
% 4.12/4.34      (![X11 : $i, X12 : $i]:
% 4.12/4.34         ((k2_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)) = (X11))),
% 4.12/4.34      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.12/4.34  thf('45', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.12/4.34         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 4.12/4.34           = (X2))),
% 4.12/4.34      inference('sup+', [status(thm)], ['43', '44'])).
% 4.12/4.34  thf('46', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i]:
% 4.12/4.34         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 4.12/4.34      inference('sup+', [status(thm)], ['42', '45'])).
% 4.12/4.34  thf('47', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i]:
% 4.12/4.34         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 4.12/4.34      inference('demod', [status(thm)], ['41', '46'])).
% 4.12/4.34  thf('48', plain,
% 4.12/4.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.12/4.34         (((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) = (X2))
% 4.12/4.34          | (r2_hidden @ X1 @ X2)
% 4.12/4.34          | (r2_hidden @ X0 @ X2))),
% 4.12/4.34      inference('sup+', [status(thm)], ['1', '47'])).
% 4.12/4.34  thf('49', plain,
% 4.12/4.34      (((sk_C_1) != (k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 4.12/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.34  thf('50', plain,
% 4.12/4.34      ((((sk_C_1) != (sk_C_1))
% 4.12/4.34        | (r2_hidden @ sk_B @ sk_C_1)
% 4.12/4.34        | (r2_hidden @ sk_A @ sk_C_1))),
% 4.12/4.34      inference('sup-', [status(thm)], ['48', '49'])).
% 4.12/4.34  thf('51', plain,
% 4.12/4.34      (((r2_hidden @ sk_A @ sk_C_1) | (r2_hidden @ sk_B @ sk_C_1))),
% 4.12/4.34      inference('simplify', [status(thm)], ['50'])).
% 4.12/4.34  thf('52', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 4.12/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.34  thf('53', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 4.12/4.34      inference('clc', [status(thm)], ['51', '52'])).
% 4.12/4.34  thf('54', plain, ($false), inference('demod', [status(thm)], ['0', '53'])).
% 4.12/4.34  
% 4.12/4.34  % SZS output end Refutation
% 4.12/4.34  
% 4.12/4.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
