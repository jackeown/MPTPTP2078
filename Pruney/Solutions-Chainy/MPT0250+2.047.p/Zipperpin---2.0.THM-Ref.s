%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.67DxIOcmvx

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:53 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   66 (  99 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  458 ( 759 expanded)
%              Number of equality atoms :   43 (  74 expanded)
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

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
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
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('23',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','20','21','22'])).

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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.67DxIOcmvx
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:11:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 248 iterations in 0.222s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(t45_zfmisc_1, conjecture,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.45/0.67       ( r2_hidden @ A @ B ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i]:
% 0.45/0.67        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.45/0.67          ( r2_hidden @ A @ B ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.45/0.67  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(d10_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X10 : $i, X12 : $i]:
% 0.45/0.67         (((X10) = (X12))
% 0.45/0.67          | ~ (r1_tarski @ X12 @ X10)
% 0.45/0.67          | ~ (r1_tarski @ X10 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.45/0.67        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf(t100_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X13 : $i, X14 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X13 @ X14)
% 0.45/0.67           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X13 : $i, X14 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X13 @ X14)
% 0.45/0.67           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf(commutativity_k5_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.67  thf(t91_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.67       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.45/0.67           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.67           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X2)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['7', '10'])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.45/0.67           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.45/0.67           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.67           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.45/0.67      inference('demod', [status(thm)], ['11', '14'])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['6', '15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.67  thf(t98_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ X20 @ X21)
% 0.45/0.67           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ X20 @ X21)
% 0.45/0.67           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.45/0.67  thf(t7_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.45/0.67  thf('23', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['3', '20', '21', '22'])).
% 0.45/0.67  thf(t69_enumset1, axiom,
% 0.45/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf(t70_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X35 : $i, X36 : $i]:
% 0.45/0.67         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.45/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.67  thf(d1_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.67       ( ![E:$i]:
% 0.45/0.67         ( ( r2_hidden @ E @ D ) <=>
% 0.45/0.67           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_2, axiom,
% 0.45/0.67    (![E:$i,C:$i,B:$i,A:$i]:
% 0.45/0.67     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.45/0.67       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_3, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.67       ( ![E:$i]:
% 0.45/0.67         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.67         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 0.45/0.67          | (r2_hidden @ X27 @ X31)
% 0.45/0.67          | ((X31) != (k1_enumset1 @ X30 @ X29 @ X28)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.67         ((r2_hidden @ X27 @ (k1_enumset1 @ X30 @ X29 @ X28))
% 0.45/0.67          | (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30))),
% 0.45/0.67      inference('simplify', [status(thm)], ['26'])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.67          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.67      inference('sup+', [status(thm)], ['25', '27'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.67         (((X23) != (X22)) | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.45/0.67         ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X22)),
% 0.45/0.67      inference('simplify', [status(thm)], ['29'])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['28', '30'])).
% 0.45/0.67  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['24', '31'])).
% 0.45/0.67  thf(d3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.45/0.67       ( ![D:$i]:
% 0.45/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.67           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X4 @ X5)
% 0.45/0.67          | (r2_hidden @ X4 @ X6)
% 0.45/0.67          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.45/0.67         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.45/0.67      inference('simplify', [status(thm)], ['33'])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['32', '34'])).
% 0.45/0.67  thf('36', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.45/0.67      inference('sup+', [status(thm)], ['23', '35'])).
% 0.45/0.67  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
