%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fz4N35rihs

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:45 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 190 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  532 (1394 expanded)
%              Number of equality atoms :   68 ( 171 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('5',plain,(
    ! [X31: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X29 ) @ ( k1_setfam_1 @ X30 ) ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ X16 )
      | ( ( k4_xboole_0 @ X14 @ X16 )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X1 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( ( k3_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
       != ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('39',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['30','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['8','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','45'])).

thf('47',plain,(
    ! [X31: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['30','42'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fz4N35rihs
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.48/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.72  % Solved by: fo/fo7.sh
% 0.48/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.72  % done 539 iterations in 0.265s
% 0.48/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.72  % SZS output start Refutation
% 0.48/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.72  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.48/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.72  thf(t12_setfam_1, conjecture,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.72    (~( ![A:$i,B:$i]:
% 0.48/0.72        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.48/0.72    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.48/0.72  thf('0', plain,
% 0.48/0.72      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.48/0.72         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(t69_enumset1, axiom,
% 0.48/0.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.48/0.72  thf('1', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.48/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.72  thf(t41_enumset1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( k2_tarski @ A @ B ) =
% 0.48/0.72       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.48/0.72  thf('2', plain,
% 0.48/0.72      (![X17 : $i, X18 : $i]:
% 0.48/0.72         ((k2_tarski @ X17 @ X18)
% 0.48/0.72           = (k2_xboole_0 @ (k1_tarski @ X17) @ (k1_tarski @ X18)))),
% 0.48/0.72      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.48/0.72  thf('3', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((k2_tarski @ X0 @ X1)
% 0.48/0.72           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.48/0.72      inference('sup+', [status(thm)], ['1', '2'])).
% 0.48/0.72  thf('4', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.48/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.72  thf(t11_setfam_1, axiom,
% 0.48/0.72    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.48/0.72  thf('5', plain, (![X31 : $i]: ((k1_setfam_1 @ (k1_tarski @ X31)) = (X31))),
% 0.48/0.72      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.48/0.72  thf('6', plain, (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.48/0.72      inference('sup+', [status(thm)], ['4', '5'])).
% 0.48/0.72  thf(t10_setfam_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.48/0.72          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.48/0.72            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.48/0.72  thf('7', plain,
% 0.48/0.72      (![X29 : $i, X30 : $i]:
% 0.48/0.72         (((X29) = (k1_xboole_0))
% 0.48/0.72          | ((k1_setfam_1 @ (k2_xboole_0 @ X29 @ X30))
% 0.48/0.72              = (k3_xboole_0 @ (k1_setfam_1 @ X29) @ (k1_setfam_1 @ X30)))
% 0.48/0.72          | ((X30) = (k1_xboole_0)))),
% 0.48/0.72      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.48/0.72  thf('8', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         (((k1_setfam_1 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 0.48/0.72            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.48/0.72          | ((X1) = (k1_xboole_0))
% 0.48/0.72          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 0.48/0.72      inference('sup+', [status(thm)], ['6', '7'])).
% 0.48/0.72  thf('9', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.48/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.72  thf(idempotence_k3_xboole_0, axiom,
% 0.48/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.48/0.72  thf('10', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.48/0.72      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.72  thf(t48_xboole_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.72  thf('11', plain,
% 0.48/0.72      (![X12 : $i, X13 : $i]:
% 0.48/0.72         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.48/0.72           = (k3_xboole_0 @ X12 @ X13))),
% 0.48/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.48/0.72  thf('12', plain,
% 0.48/0.72      (![X12 : $i, X13 : $i]:
% 0.48/0.72         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.48/0.72           = (k3_xboole_0 @ X12 @ X13))),
% 0.48/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.48/0.72  thf('13', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.48/0.72           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.48/0.72      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.72  thf('14', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((k4_xboole_0 @ X0 @ X0)
% 0.48/0.72           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.48/0.72      inference('sup+', [status(thm)], ['10', '13'])).
% 0.48/0.72  thf('15', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.48/0.72      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.72  thf('16', plain,
% 0.48/0.72      (![X12 : $i, X13 : $i]:
% 0.48/0.72         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.48/0.72           = (k3_xboole_0 @ X12 @ X13))),
% 0.48/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.48/0.72  thf(t83_xboole_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.48/0.72  thf('17', plain,
% 0.48/0.72      (![X14 : $i, X16 : $i]:
% 0.48/0.72         ((r1_xboole_0 @ X14 @ X16) | ((k4_xboole_0 @ X14 @ X16) != (X14)))),
% 0.48/0.72      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.48/0.72  thf('18', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         (((k3_xboole_0 @ X1 @ X0) != (X1))
% 0.48/0.72          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.72  thf('19', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (((X0) != (X0)) | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['15', '18'])).
% 0.48/0.72  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['19'])).
% 0.48/0.72  thf(d7_xboole_0, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.48/0.72       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.72  thf('21', plain,
% 0.48/0.72      (![X2 : $i, X3 : $i]:
% 0.48/0.72         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.48/0.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.48/0.72  thf('22', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.72  thf('23', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((k4_xboole_0 @ X0 @ X0)
% 0.48/0.72           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.48/0.72      inference('sup+', [status(thm)], ['10', '13'])).
% 0.48/0.72  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.72      inference('sup+', [status(thm)], ['22', '23'])).
% 0.48/0.72  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.72      inference('sup+', [status(thm)], ['22', '23'])).
% 0.48/0.72  thf('26', plain,
% 0.48/0.72      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.72      inference('demod', [status(thm)], ['14', '24', '25'])).
% 0.48/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.72  thf('27', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.72  thf(l29_zfmisc_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.48/0.72       ( r2_hidden @ B @ A ) ))).
% 0.48/0.72  thf('28', plain,
% 0.48/0.72      (![X25 : $i, X26 : $i]:
% 0.48/0.72         ((r2_hidden @ X25 @ X26)
% 0.48/0.72          | ((k3_xboole_0 @ X26 @ (k1_tarski @ X25)) != (k1_tarski @ X25)))),
% 0.48/0.72      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.48/0.72  thf('29', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) != (k1_tarski @ X1))
% 0.48/0.72          | (r2_hidden @ X1 @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.72  thf('30', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['26', '29'])).
% 0.48/0.72  thf(t21_xboole_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.48/0.72  thf('31', plain,
% 0.48/0.72      (![X10 : $i, X11 : $i]:
% 0.48/0.72         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (X10))),
% 0.48/0.72      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.48/0.72  thf('32', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.72  thf('33', plain,
% 0.48/0.72      (![X2 : $i, X4 : $i]:
% 0.48/0.72         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.48/0.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.48/0.72  thf('34', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['32', '33'])).
% 0.48/0.72  thf('35', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         (((X0) != (k1_xboole_0))
% 0.48/0.72          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['31', '34'])).
% 0.48/0.72  thf('36', plain,
% 0.48/0.72      (![X1 : $i]:
% 0.48/0.72         (r1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ k1_xboole_0)),
% 0.48/0.72      inference('simplify', [status(thm)], ['35'])).
% 0.48/0.72  thf('37', plain,
% 0.48/0.72      (![X10 : $i, X11 : $i]:
% 0.48/0.72         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (X10))),
% 0.48/0.72      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.48/0.72  thf('38', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.72  thf(t4_xboole_0, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.48/0.72            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.48/0.72  thf('39', plain,
% 0.48/0.72      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.48/0.72         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.48/0.72          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.48/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.48/0.72  thf('40', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.48/0.72          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['38', '39'])).
% 0.48/0.72  thf('41', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (~ (r2_hidden @ X2 @ X0)
% 0.48/0.72          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['37', '40'])).
% 0.48/0.72  thf('42', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.48/0.72      inference('sup-', [status(thm)], ['36', '41'])).
% 0.48/0.72  thf('43', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.48/0.72      inference('clc', [status(thm)], ['30', '42'])).
% 0.48/0.72  thf('44', plain, (![X0 : $i]: ((k1_xboole_0) != (k2_tarski @ X0 @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['9', '43'])).
% 0.48/0.72  thf('45', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         (((X1) = (k1_xboole_0))
% 0.48/0.72          | ((k1_setfam_1 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 0.48/0.72              = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1))))),
% 0.48/0.72      inference('clc', [status(thm)], ['8', '44'])).
% 0.48/0.72  thf('46', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.48/0.72            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.48/0.72          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.48/0.72      inference('sup+', [status(thm)], ['3', '45'])).
% 0.48/0.72  thf('47', plain, (![X31 : $i]: ((k1_setfam_1 @ (k1_tarski @ X31)) = (X31))),
% 0.48/0.72      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.48/0.72  thf('48', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.48/0.72          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.48/0.72      inference('demod', [status(thm)], ['46', '47'])).
% 0.48/0.72  thf('49', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.48/0.72      inference('clc', [status(thm)], ['30', '42'])).
% 0.48/0.72  thf('50', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.48/0.72      inference('clc', [status(thm)], ['48', '49'])).
% 0.48/0.72  thf('51', plain,
% 0.48/0.72      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.48/0.72      inference('demod', [status(thm)], ['0', '50'])).
% 0.48/0.72  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.48/0.72  
% 0.48/0.72  % SZS output end Refutation
% 0.48/0.72  
% 0.56/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
