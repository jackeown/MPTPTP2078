%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BrmIaq0U27

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:46 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 388 expanded)
%              Number of leaves         :   25 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :  496 (3344 expanded)
%              Number of equality atoms :   74 ( 501 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['3'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('6',plain,(
    ! [X39: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X37 @ X38 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X37 ) @ ( k1_setfam_1 @ X38 ) ) )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X39: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('15',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
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

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X39: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('31',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['3'])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('34',plain,(
    ! [X39: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('35',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_B ),
    inference(clc,[status(thm)],['38','41'])).

thf('43',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['17','28'])).

thf('46',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['29','30'])).

thf('47',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['31','42'])).

thf('48',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('49',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','43','44','45','46','47','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BrmIaq0U27
% 0.15/0.37  % Computer   : n015.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:54:38 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 196 iterations in 0.116s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.41/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.41/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.60  thf(t12_setfam_1, conjecture,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i]:
% 0.41/0.60        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.41/0.60         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.41/0.60  thf('1', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.41/0.60  thf(d7_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.41/0.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X0 : $i, X2 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('4', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('simplify', [status(thm)], ['3'])).
% 0.41/0.60  thf(t41_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k2_tarski @ A @ B ) =
% 0.41/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i]:
% 0.41/0.60         ((k2_tarski @ X16 @ X17)
% 0.41/0.60           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.41/0.60  thf(t11_setfam_1, axiom,
% 0.41/0.60    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.41/0.60  thf('6', plain, (![X39 : $i]: ((k1_setfam_1 @ (k1_tarski @ X39)) = (X39))),
% 0.41/0.60      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.41/0.60  thf(t10_setfam_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.41/0.60          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.41/0.60            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X37 : $i, X38 : $i]:
% 0.41/0.60         (((X37) = (k1_xboole_0))
% 0.41/0.60          | ((k1_setfam_1 @ (k2_xboole_0 @ X37 @ X38))
% 0.41/0.60              = (k3_xboole_0 @ (k1_setfam_1 @ X37) @ (k1_setfam_1 @ X38)))
% 0.41/0.60          | ((X38) = (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.41/0.60            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.41/0.60          | ((X1) = (k1_xboole_0))
% 0.41/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['6', '7'])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.41/0.60            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.41/0.60          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.41/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['5', '8'])).
% 0.41/0.60  thf('10', plain, (![X39 : $i]: ((k1_setfam_1 @ (k1_tarski @ X39)) = (X39))),
% 0.41/0.60      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.41/0.60          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.41/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.41/0.60         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.41/0.60        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.41/0.60        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.41/0.60        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.41/0.60  thf(l24_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X33 : $i, X34 : $i]:
% 0.41/0.60         (~ (r1_xboole_0 @ (k1_tarski @ X33) @ X34) | ~ (r2_hidden @ X33 @ X34))),
% 0.41/0.60      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.60          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.41/0.60          | ~ (r2_hidden @ sk_B @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      ((~ (r2_hidden @ sk_B @ k1_xboole_0)
% 0.41/0.60        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '16'])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.41/0.60        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.41/0.60  thf(t69_enumset1, axiom,
% 0.41/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.41/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.60  thf(t70_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X28 : $i, X29 : $i]:
% 0.41/0.60         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.60  thf(d1_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.41/0.60       ( ![E:$i]:
% 0.41/0.60         ( ( r2_hidden @ E @ D ) <=>
% 0.41/0.60           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.41/0.60  thf(zf_stmt_2, axiom,
% 0.41/0.60    (![E:$i,C:$i,B:$i,A:$i]:
% 0.41/0.60     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.41/0.60       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_3, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.41/0.60       ( ![E:$i]:
% 0.41/0.60         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.60         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.41/0.60          | (r2_hidden @ X9 @ X13)
% 0.41/0.60          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.60         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.41/0.60          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.41/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.41/0.60          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['20', '22'])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.60         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.41/0.60      inference('simplify', [status(thm)], ['24'])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['23', '25'])).
% 0.41/0.60  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['19', '26'])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (((r2_hidden @ sk_B @ k1_xboole_0) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['18', '27'])).
% 0.41/0.60  thf('29', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.41/0.60      inference('clc', [status(thm)], ['17', '28'])).
% 0.41/0.60  thf('30', plain, (![X39 : $i]: ((k1_setfam_1 @ (k1_tarski @ X39)) = (X39))),
% 0.41/0.60      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.41/0.60  thf('31', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('32', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('simplify', [status(thm)], ['3'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.41/0.60        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.41/0.60  thf('34', plain, (![X39 : $i]: ((k1_setfam_1 @ (k1_tarski @ X39)) = (X39))),
% 0.41/0.60      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.41/0.60        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (![X33 : $i, X34 : $i]:
% 0.41/0.60         (~ (r1_xboole_0 @ (k1_tarski @ X33) @ X34) | ~ (r2_hidden @ X33 @ X34))),
% 0.41/0.60      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.60          | ((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.41/0.60          | ~ (r2_hidden @ sk_A @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      ((~ (r2_hidden @ sk_A @ k1_xboole_0)
% 0.41/0.60        | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['32', '37'])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.41/0.60        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('40', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['19', '26'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.41/0.60        | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('42', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_B))),
% 0.41/0.60      inference('clc', [status(thm)], ['38', '41'])).
% 0.41/0.60  thf('43', plain, (((sk_A) = (sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['31', '42'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.41/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.60  thf('45', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.41/0.60      inference('clc', [status(thm)], ['17', '28'])).
% 0.41/0.60  thf('46', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('47', plain, (((sk_A) = (sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['31', '42'])).
% 0.41/0.60  thf('48', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.41/0.60  thf('49', plain, (((sk_A) != (sk_A))),
% 0.41/0.60      inference('demod', [status(thm)],
% 0.41/0.60                ['0', '43', '44', '45', '46', '47', '48'])).
% 0.41/0.60  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
