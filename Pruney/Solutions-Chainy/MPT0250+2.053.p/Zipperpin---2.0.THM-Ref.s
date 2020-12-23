%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9Lhhi7rLDJ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:54 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   66 (  78 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  450 ( 562 expanded)
%              Number of equality atoms :   39 (  49 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_xboole_0 @ X10 @ X12 )
      | ( X10 = X12 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r2_xboole_0 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('6',plain,(
    ~ ( r2_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ~ ( r2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','21'])).

thf('23',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
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

thf('26',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X27 @ X31 )
      | ( X31
       != ( k1_enumset1 @ X30 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ ( k1_enumset1 @ X30 @ X29 @ X28 ) )
      | ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X22 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('34',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['23','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9Lhhi7rLDJ
% 0.13/0.36  % Computer   : n015.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:19:23 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.59/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.76  % Solved by: fo/fo7.sh
% 0.59/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.76  % done 290 iterations in 0.321s
% 0.59/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.76  % SZS output start Refutation
% 0.59/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.76  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.59/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.59/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.76  thf(t45_zfmisc_1, conjecture,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.59/0.76       ( r2_hidden @ A @ B ) ))).
% 0.59/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.76    (~( ![A:$i,B:$i]:
% 0.59/0.76        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.59/0.76          ( r2_hidden @ A @ B ) ) )),
% 0.59/0.76    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.59/0.76  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(t7_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.76  thf('1', plain,
% 0.59/0.76      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.59/0.76      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.76  thf(d8_xboole_0, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.59/0.76       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.59/0.76  thf('2', plain,
% 0.59/0.76      (![X10 : $i, X12 : $i]:
% 0.59/0.76         ((r2_xboole_0 @ X10 @ X12)
% 0.59/0.76          | ((X10) = (X12))
% 0.59/0.76          | ~ (r1_tarski @ X10 @ X12))),
% 0.59/0.76      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.59/0.76  thf('3', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 0.59/0.76          | (r2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t60_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X13 : $i, X14 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X13 @ X14) | ~ (r2_xboole_0 @ X14 @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (~ (r2_xboole_0 @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.77  thf(t94_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k2_xboole_0 @ A @ B ) =
% 0.59/0.77       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      (![X20 : $i, X21 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X20 @ X21)
% 0.59/0.77           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.59/0.77              (k3_xboole_0 @ X20 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.59/0.77  thf(commutativity_k5_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.77  thf(t91_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.77       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.59/0.77           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.59/0.77           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['8', '9'])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (![X20 : $i, X21 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X20 @ X21)
% 0.59/0.77           = (k5_xboole_0 @ X21 @ 
% 0.59/0.77              (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))))),
% 0.59/0.77      inference('demod', [status(thm)], ['7', '10'])).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.59/0.77           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.59/0.77           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X1 @ X0)
% 0.59/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['11', '14'])).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X1 @ X0)
% 0.59/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16'])).
% 0.59/0.77  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X20 : $i, X21 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X20 @ X21)
% 0.59/0.77           = (k5_xboole_0 @ X21 @ 
% 0.59/0.77              (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))))),
% 0.59/0.77      inference('demod', [status(thm)], ['7', '10'])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X0 @ X1)
% 0.59/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.59/0.77      inference('sup+', [status(thm)], ['18', '19'])).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['17', '20'])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (~ (r2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['6', '21'])).
% 0.59/0.77  thf('23', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['3', '22'])).
% 0.59/0.77  thf(t69_enumset1, axiom,
% 0.59/0.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.59/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.77  thf(t70_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X35 : $i, X36 : $i]:
% 0.59/0.77         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.59/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.77  thf(d1_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.77     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.59/0.77       ( ![E:$i]:
% 0.59/0.77         ( ( r2_hidden @ E @ D ) <=>
% 0.59/0.77           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.59/0.77  thf(zf_stmt_2, axiom,
% 0.59/0.77    (![E:$i,C:$i,B:$i,A:$i]:
% 0.59/0.77     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.59/0.77       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_3, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.77     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.59/0.77       ( ![E:$i]:
% 0.59/0.77         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.59/0.77         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 0.59/0.77          | (r2_hidden @ X27 @ X31)
% 0.59/0.77          | ((X31) != (k1_enumset1 @ X30 @ X29 @ X28)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.77  thf('27', plain,
% 0.59/0.77      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.77         ((r2_hidden @ X27 @ (k1_enumset1 @ X30 @ X29 @ X28))
% 0.59/0.77          | (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30))),
% 0.59/0.77      inference('simplify', [status(thm)], ['26'])).
% 0.59/0.77  thf('28', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.59/0.77          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.59/0.77      inference('sup+', [status(thm)], ['25', '27'])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.59/0.77         (((X23) != (X22)) | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.77  thf('30', plain,
% 0.59/0.77      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.59/0.77         ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X22)),
% 0.59/0.77      inference('simplify', [status(thm)], ['29'])).
% 0.59/0.77  thf('31', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['28', '30'])).
% 0.59/0.77  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['24', '31'])).
% 0.59/0.77  thf(d3_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.59/0.77       ( ![D:$i]:
% 0.59/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.77           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.59/0.77  thf('33', plain,
% 0.59/0.77      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X4 @ X5)
% 0.59/0.77          | (r2_hidden @ X4 @ X6)
% 0.59/0.77          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.59/0.77  thf('34', plain,
% 0.59/0.77      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.59/0.77         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.59/0.77      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.77  thf('35', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['32', '34'])).
% 0.59/0.77  thf('36', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.59/0.77      inference('sup+', [status(thm)], ['23', '35'])).
% 0.59/0.77  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
