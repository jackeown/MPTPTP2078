%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WuQnPo4UXK

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:19 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   52 (  75 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :  353 ( 560 expanded)
%              Number of equality atoms :   31 (  52 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    | ( sk_C
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('15',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','12','13','14'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['15','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WuQnPo4UXK
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 247 iterations in 0.431s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.89  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.70/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.70/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(t47_zfmisc_1, conjecture,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.70/0.89       ( r2_hidden @ A @ C ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.89        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.70/0.89          ( r2_hidden @ A @ C ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.70/0.89  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(d10_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X10 : $i, X12 : $i]:
% 0.70/0.89         (((X10) = (X12))
% 0.70/0.89          | ~ (r1_tarski @ X12 @ X10)
% 0.70/0.89          | ~ (r1_tarski @ X10 @ X12))),
% 0.70/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.70/0.89        | ((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf(commutativity_k5_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.70/0.89  thf('4', plain,
% 0.70/0.89      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.70/0.89  thf(t94_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k2_xboole_0 @ A @ B ) =
% 0.70/0.89       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      (![X18 : $i, X19 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X18 @ X19)
% 0.70/0.89           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.70/0.89              (k3_xboole_0 @ X18 @ X19)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      (![X18 : $i, X19 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X18 @ X19)
% 0.70/0.89           = (k5_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 0.70/0.89              (k5_xboole_0 @ X18 @ X19)))),
% 0.70/0.89      inference('demod', [status(thm)], ['5', '6'])).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X0 @ X1)
% 0.70/0.89           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['4', '7'])).
% 0.70/0.89  thf(commutativity_k3_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      (![X18 : $i, X19 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X18 @ X19)
% 0.70/0.89           = (k5_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 0.70/0.89              (k5_xboole_0 @ X18 @ X19)))),
% 0.70/0.89      inference('demod', [status(thm)], ['5', '6'])).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X0 @ X1)
% 0.70/0.89           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.70/0.89  thf('12', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['8', '11'])).
% 0.70/0.89  thf(t7_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.70/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['8', '11'])).
% 0.70/0.89  thf('15', plain,
% 0.70/0.89      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['3', '12', '13', '14'])).
% 0.70/0.89  thf(t70_enumset1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.70/0.89  thf('16', plain,
% 0.70/0.89      (![X32 : $i, X33 : $i]:
% 0.70/0.89         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.70/0.89      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.70/0.89  thf(d1_enumset1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.70/0.89       ( ![E:$i]:
% 0.70/0.89         ( ( r2_hidden @ E @ D ) <=>
% 0.70/0.89           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.70/0.89  thf(zf_stmt_2, axiom,
% 0.70/0.89    (![E:$i,C:$i,B:$i,A:$i]:
% 0.70/0.89     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.70/0.89       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_3, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.70/0.89       ( ![E:$i]:
% 0.70/0.89         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.70/0.89  thf('17', plain,
% 0.70/0.89      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.70/0.89         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 0.70/0.89          | (r2_hidden @ X25 @ X29)
% 0.70/0.89          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.70/0.89         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 0.70/0.89          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 0.70/0.89      inference('simplify', [status(thm)], ['17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.70/0.89          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.70/0.89      inference('sup+', [status(thm)], ['16', '18'])).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.70/0.89         (((X21) != (X20)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.70/0.89         ~ (zip_tseitin_0 @ X20 @ X22 @ X23 @ X20)),
% 0.70/0.89      inference('simplify', [status(thm)], ['20'])).
% 0.70/0.89  thf('22', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['19', '21'])).
% 0.70/0.89  thf(d3_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.70/0.89       ( ![D:$i]:
% 0.70/0.89         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.89           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.70/0.89  thf('23', plain,
% 0.70/0.89      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X4 @ X5)
% 0.70/0.89          | (r2_hidden @ X4 @ X6)
% 0.70/0.89          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.70/0.89         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.70/0.89      inference('simplify', [status(thm)], ['23'])).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (r2_hidden @ X1 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['22', '24'])).
% 0.70/0.89  thf('26', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.70/0.89      inference('sup+', [status(thm)], ['15', '25'])).
% 0.70/0.89  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.74/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
