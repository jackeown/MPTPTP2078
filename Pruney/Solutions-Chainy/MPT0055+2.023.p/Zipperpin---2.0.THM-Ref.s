%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NyMeMswW5s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:16 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   61 (  69 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  453 ( 557 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k3_xboole_0 @ X28 @ X29 ) )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X26 @ X27 ) @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X12 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_xboole_0 @ X21 @ X20 )
        = X20 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k3_xboole_0 @ X28 @ X29 ) )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['4','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NyMeMswW5s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.86/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.86/1.04  % Solved by: fo/fo7.sh
% 0.86/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.04  % done 1147 iterations in 0.593s
% 0.86/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.86/1.04  % SZS output start Refutation
% 0.86/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.86/1.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.86/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.86/1.04  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.86/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.86/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.86/1.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.86/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.86/1.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.86/1.04  thf(t48_xboole_1, conjecture,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.86/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.04    (~( ![A:$i,B:$i]:
% 0.86/1.04        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 0.86/1.04          ( k3_xboole_0 @ A @ B ) ) )),
% 0.86/1.04    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 0.86/1.04  thf('0', plain,
% 0.86/1.04      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.86/1.04         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf(t47_xboole_1, axiom,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.86/1.04  thf('1', plain,
% 0.86/1.04      (![X28 : $i, X29 : $i]:
% 0.86/1.04         ((k4_xboole_0 @ X28 @ (k3_xboole_0 @ X28 @ X29))
% 0.86/1.04           = (k4_xboole_0 @ X28 @ X29))),
% 0.86/1.04      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.86/1.04  thf(t39_xboole_1, axiom,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.86/1.04  thf('2', plain,
% 0.86/1.04      (![X24 : $i, X25 : $i]:
% 0.86/1.04         ((k2_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24))
% 0.86/1.04           = (k2_xboole_0 @ X24 @ X25))),
% 0.86/1.04      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.86/1.04  thf(t40_xboole_1, axiom,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.86/1.04  thf('3', plain,
% 0.86/1.04      (![X26 : $i, X27 : $i]:
% 0.86/1.04         ((k4_xboole_0 @ (k2_xboole_0 @ X26 @ X27) @ X27)
% 0.86/1.04           = (k4_xboole_0 @ X26 @ X27))),
% 0.86/1.04      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.86/1.04  thf('4', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i]:
% 0.86/1.04         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.86/1.04           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf(t3_xboole_0, axiom,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.86/1.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.86/1.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.86/1.04            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.86/1.04  thf('5', plain,
% 0.86/1.04      (![X12 : $i, X13 : $i]:
% 0.86/1.04         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X13))),
% 0.86/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.86/1.04  thf('6', plain,
% 0.86/1.04      (![X12 : $i, X13 : $i]:
% 0.86/1.04         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X12))),
% 0.86/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.86/1.04  thf(d5_xboole_0, axiom,
% 0.86/1.04    (![A:$i,B:$i,C:$i]:
% 0.86/1.04     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.86/1.04       ( ![D:$i]:
% 0.86/1.04         ( ( r2_hidden @ D @ C ) <=>
% 0.86/1.04           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.86/1.04  thf('7', plain,
% 0.86/1.04      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.86/1.04         (~ (r2_hidden @ X10 @ X9)
% 0.86/1.04          | ~ (r2_hidden @ X10 @ X8)
% 0.86/1.04          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.86/1.04      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.86/1.04  thf('8', plain,
% 0.86/1.04      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.86/1.04         (~ (r2_hidden @ X10 @ X8)
% 0.86/1.04          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.86/1.04      inference('simplify', [status(thm)], ['7'])).
% 0.86/1.04  thf('9', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.04         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.86/1.04          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.86/1.04      inference('sup-', [status(thm)], ['6', '8'])).
% 0.86/1.04  thf('10', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i]:
% 0.86/1.04         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.86/1.04          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.86/1.04      inference('sup-', [status(thm)], ['5', '9'])).
% 0.86/1.04  thf('11', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.86/1.04      inference('simplify', [status(thm)], ['10'])).
% 0.86/1.04  thf('12', plain,
% 0.86/1.04      (![X12 : $i, X13 : $i]:
% 0.86/1.04         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X12))),
% 0.86/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.86/1.04  thf('13', plain,
% 0.86/1.04      (![X12 : $i, X13 : $i]:
% 0.86/1.04         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X13))),
% 0.86/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.86/1.04  thf('14', plain,
% 0.86/1.04      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.86/1.04         (~ (r2_hidden @ X14 @ X12)
% 0.86/1.04          | ~ (r2_hidden @ X14 @ X15)
% 0.86/1.04          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.86/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.86/1.04  thf('15', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.04         ((r1_xboole_0 @ X1 @ X0)
% 0.86/1.04          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.86/1.04          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.86/1.04      inference('sup-', [status(thm)], ['13', '14'])).
% 0.86/1.04  thf('16', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i]:
% 0.86/1.04         ((r1_xboole_0 @ X0 @ X1)
% 0.86/1.04          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.86/1.04          | (r1_xboole_0 @ X0 @ X1))),
% 0.86/1.04      inference('sup-', [status(thm)], ['12', '15'])).
% 0.86/1.04  thf('17', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i]:
% 0.86/1.04         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.86/1.04      inference('simplify', [status(thm)], ['16'])).
% 0.86/1.04  thf('18', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.86/1.04      inference('sup-', [status(thm)], ['11', '17'])).
% 0.86/1.04  thf(d3_tarski, axiom,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( r1_tarski @ A @ B ) <=>
% 0.86/1.04       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.86/1.04  thf('19', plain,
% 0.86/1.04      (![X3 : $i, X5 : $i]:
% 0.86/1.04         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_tarski])).
% 0.86/1.04  thf(t4_xboole_0, axiom,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.86/1.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.86/1.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.86/1.04            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.86/1.04  thf('20', plain,
% 0.86/1.04      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.86/1.04         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 0.86/1.04          | ~ (r1_xboole_0 @ X16 @ X19))),
% 0.86/1.04      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.86/1.04  thf('21', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.04         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.86/1.04          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.86/1.04      inference('sup-', [status(thm)], ['19', '20'])).
% 0.86/1.04  thf('22', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.04         (r1_tarski @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)),
% 0.86/1.04      inference('sup-', [status(thm)], ['18', '21'])).
% 0.86/1.04  thf(t12_xboole_1, axiom,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.86/1.04  thf('23', plain,
% 0.86/1.04      (![X20 : $i, X21 : $i]:
% 0.86/1.04         (((k2_xboole_0 @ X21 @ X20) = (X20)) | ~ (r1_tarski @ X21 @ X20))),
% 0.86/1.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.86/1.04  thf('24', plain,
% 0.86/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.04         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1)) @ X0)
% 0.86/1.05           = (X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['22', '23'])).
% 0.86/1.05  thf('25', plain,
% 0.86/1.05      (![X28 : $i, X29 : $i]:
% 0.86/1.05         ((k4_xboole_0 @ X28 @ (k3_xboole_0 @ X28 @ X29))
% 0.86/1.05           = (k4_xboole_0 @ X28 @ X29))),
% 0.86/1.05      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.86/1.05  thf('26', plain,
% 0.86/1.05      (![X24 : $i, X25 : $i]:
% 0.86/1.05         ((k2_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24))
% 0.86/1.05           = (k2_xboole_0 @ X24 @ X25))),
% 0.86/1.05      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.86/1.05  thf('27', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.86/1.05           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.86/1.05      inference('sup+', [status(thm)], ['25', '26'])).
% 0.86/1.05  thf(commutativity_k2_xboole_0, axiom,
% 0.86/1.05    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.86/1.05  thf('28', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.86/1.05  thf(t22_xboole_1, axiom,
% 0.86/1.05    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.86/1.05  thf('29', plain,
% 0.86/1.05      (![X22 : $i, X23 : $i]:
% 0.86/1.05         ((k2_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)) = (X22))),
% 0.86/1.05      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.86/1.05  thf('30', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.86/1.05           = (X1))),
% 0.86/1.05      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.86/1.05  thf('31', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.86/1.05      inference('sup+', [status(thm)], ['24', '30'])).
% 0.86/1.05  thf('32', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.86/1.05           = (X1))),
% 0.86/1.05      inference('demod', [status(thm)], ['4', '31'])).
% 0.86/1.05  thf('33', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.86/1.05           (k4_xboole_0 @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.86/1.05      inference('sup+', [status(thm)], ['1', '32'])).
% 0.86/1.05  thf('34', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.86/1.05  thf('35', plain,
% 0.86/1.05      (![X22 : $i, X23 : $i]:
% 0.86/1.05         ((k2_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)) = (X22))),
% 0.86/1.05      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.86/1.05  thf('36', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.86/1.05           = (k3_xboole_0 @ X1 @ X0))),
% 0.86/1.05      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.86/1.05  thf('37', plain,
% 0.86/1.05      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.86/1.05      inference('demod', [status(thm)], ['0', '36'])).
% 0.86/1.05  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.86/1.05  
% 0.86/1.05  % SZS output end Refutation
% 0.86/1.05  
% 0.86/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
