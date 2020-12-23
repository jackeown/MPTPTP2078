%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.756wohSiXU

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:16 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 110 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  469 ( 781 expanded)
%              Number of equality atoms :   44 (  86 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('30',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','30'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','33'])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['4','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.756wohSiXU
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.91  % Solved by: fo/fo7.sh
% 0.66/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.91  % done 1339 iterations in 0.458s
% 0.66/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.91  % SZS output start Refutation
% 0.66/0.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.66/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.66/0.91  thf(t48_xboole_1, conjecture,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.66/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.91    (~( ![A:$i,B:$i]:
% 0.66/0.91        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 0.66/0.91          ( k3_xboole_0 @ A @ B ) ) )),
% 0.66/0.91    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 0.66/0.91  thf('0', plain,
% 0.66/0.91      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.66/0.91         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf(t47_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.66/0.91  thf('1', plain,
% 0.66/0.91      (![X23 : $i, X24 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.66/0.91           = (k4_xboole_0 @ X23 @ X24))),
% 0.66/0.91      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.66/0.91  thf(t39_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.66/0.91  thf('2', plain,
% 0.66/0.91      (![X19 : $i, X20 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.66/0.91           = (k2_xboole_0 @ X19 @ X20))),
% 0.66/0.91      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.66/0.91  thf(t40_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.66/0.91  thf('3', plain,
% 0.66/0.91      (![X21 : $i, X22 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22)
% 0.66/0.91           = (k4_xboole_0 @ X21 @ X22))),
% 0.66/0.91      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.66/0.91  thf('4', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.66/0.91           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['2', '3'])).
% 0.66/0.91  thf(t3_xboole_0, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.66/0.91            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.66/0.91       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.66/0.91            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.66/0.91  thf('5', plain,
% 0.66/0.91      (![X8 : $i, X9 : $i]:
% 0.66/0.91         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.66/0.91      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.66/0.91  thf('6', plain,
% 0.66/0.91      (![X8 : $i, X9 : $i]:
% 0.66/0.91         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.66/0.91      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.66/0.91  thf(d5_xboole_0, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.66/0.91       ( ![D:$i]:
% 0.66/0.91         ( ( r2_hidden @ D @ C ) <=>
% 0.66/0.91           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.66/0.91  thf('7', plain,
% 0.66/0.91      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X6 @ X5)
% 0.66/0.91          | ~ (r2_hidden @ X6 @ X4)
% 0.66/0.91          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.66/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.66/0.91  thf('8', plain,
% 0.66/0.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X6 @ X4)
% 0.66/0.91          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.66/0.91      inference('simplify', [status(thm)], ['7'])).
% 0.66/0.91  thf('9', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.66/0.91          | ~ (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['6', '8'])).
% 0.66/0.91  thf('10', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.66/0.91          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['5', '9'])).
% 0.66/0.91  thf('11', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.66/0.91      inference('simplify', [status(thm)], ['10'])).
% 0.66/0.91  thf('12', plain,
% 0.66/0.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.66/0.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.66/0.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.66/0.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.66/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.66/0.91  thf(commutativity_k2_xboole_0, axiom,
% 0.66/0.91    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.66/0.91  thf('13', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.66/0.91  thf(t1_boole, axiom,
% 0.66/0.91    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.91  thf('14', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.66/0.91      inference('cnf', [status(esa)], [t1_boole])).
% 0.66/0.91  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['13', '14'])).
% 0.66/0.91  thf('16', plain,
% 0.66/0.91      (![X19 : $i, X20 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.66/0.91           = (k2_xboole_0 @ X19 @ X20))),
% 0.66/0.91      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.66/0.91  thf('17', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['15', '16'])).
% 0.66/0.91  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['13', '14'])).
% 0.66/0.91  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['17', '18'])).
% 0.66/0.91  thf('20', plain,
% 0.66/0.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X6 @ X4)
% 0.66/0.91          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.66/0.91      inference('simplify', [status(thm)], ['7'])).
% 0.66/0.91  thf('21', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['19', '20'])).
% 0.66/0.91  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.66/0.91      inference('condensation', [status(thm)], ['21'])).
% 0.66/0.91  thf('23', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.66/0.91          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['12', '22'])).
% 0.66/0.91  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['13', '14'])).
% 0.66/0.91  thf(t22_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.66/0.91  thf('25', plain,
% 0.66/0.91      (![X17 : $i, X18 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)) = (X17))),
% 0.66/0.91      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.66/0.91  thf('26', plain,
% 0.66/0.91      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['24', '25'])).
% 0.66/0.91  thf('27', plain,
% 0.66/0.91      (![X23 : $i, X24 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.66/0.91           = (k4_xboole_0 @ X23 @ X24))),
% 0.66/0.91      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.66/0.91  thf('28', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.66/0.91           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['26', '27'])).
% 0.66/0.91  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['17', '18'])).
% 0.66/0.91  thf('30', plain,
% 0.66/0.91      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['28', '29'])).
% 0.66/0.91  thf('31', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.66/0.91          | ((X1) = (k1_xboole_0)))),
% 0.66/0.91      inference('demod', [status(thm)], ['23', '30'])).
% 0.66/0.91  thf(t4_xboole_0, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.66/0.91            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.66/0.91       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.66/0.91            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.66/0.91  thf('32', plain,
% 0.66/0.91      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 0.66/0.91          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.66/0.91      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.66/0.91  thf('33', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['31', '32'])).
% 0.66/0.91  thf('34', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['11', '33'])).
% 0.66/0.91  thf('35', plain,
% 0.66/0.91      (![X23 : $i, X24 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.66/0.91           = (k4_xboole_0 @ X23 @ X24))),
% 0.66/0.91      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.66/0.91  thf('36', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.66/0.91           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.91  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['17', '18'])).
% 0.66/0.91  thf('38', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('demod', [status(thm)], ['36', '37'])).
% 0.66/0.91  thf('39', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.66/0.91           = (X1))),
% 0.66/0.91      inference('demod', [status(thm)], ['4', '38'])).
% 0.66/0.91  thf('40', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.66/0.91           (k4_xboole_0 @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['1', '39'])).
% 0.66/0.91  thf('41', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.66/0.91  thf('42', plain,
% 0.66/0.91      (![X17 : $i, X18 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)) = (X17))),
% 0.66/0.91      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.66/0.91  thf('43', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.66/0.91           = (k3_xboole_0 @ X1 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.66/0.91  thf('44', plain,
% 0.66/0.91      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.66/0.91      inference('demod', [status(thm)], ['0', '43'])).
% 0.66/0.91  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.66/0.91  
% 0.66/0.91  % SZS output end Refutation
% 0.66/0.91  
% 0.66/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
