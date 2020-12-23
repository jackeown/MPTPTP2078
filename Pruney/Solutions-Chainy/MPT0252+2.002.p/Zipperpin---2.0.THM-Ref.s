%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OPYhPxHjdN

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:16 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  56 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  298 ( 380 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X18: $i] :
      ( ( X16 = X18 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
    | ( sk_C_1
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_tarski @ X32 @ X31 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,
    ( sk_C_1
    = ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','8','9','10'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
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

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 )
      | ( r2_hidden @ X38 @ X42 )
      | ( X42
       != ( k1_enumset1 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X38 @ ( k1_enumset1 @ X41 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X34 != X33 )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X33 @ X35 @ X36 @ X33 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['11','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OPYhPxHjdN
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:12:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.22/2.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.22/2.40  % Solved by: fo/fo7.sh
% 2.22/2.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.22/2.40  % done 2118 iterations in 1.942s
% 2.22/2.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.22/2.40  % SZS output start Refutation
% 2.22/2.40  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.22/2.40  thf(sk_B_type, type, sk_B: $i).
% 2.22/2.40  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.22/2.40  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.22/2.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.22/2.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.22/2.40  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.22/2.40  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.22/2.40  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.22/2.40  thf(sk_A_type, type, sk_A: $i).
% 2.22/2.40  thf(t47_zfmisc_1, conjecture,
% 2.22/2.40    (![A:$i,B:$i,C:$i]:
% 2.22/2.40     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 2.22/2.40       ( r2_hidden @ A @ C ) ))).
% 2.22/2.40  thf(zf_stmt_0, negated_conjecture,
% 2.22/2.40    (~( ![A:$i,B:$i,C:$i]:
% 2.22/2.40        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 2.22/2.40          ( r2_hidden @ A @ C ) ) )),
% 2.22/2.40    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 2.22/2.40  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf('1', plain,
% 2.22/2.40      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf(d10_xboole_0, axiom,
% 2.22/2.40    (![A:$i,B:$i]:
% 2.22/2.40     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.22/2.40  thf('2', plain,
% 2.22/2.40      (![X16 : $i, X18 : $i]:
% 2.22/2.40         (((X16) = (X18))
% 2.22/2.40          | ~ (r1_tarski @ X18 @ X16)
% 2.22/2.40          | ~ (r1_tarski @ X16 @ X18))),
% 2.22/2.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.22/2.40  thf('3', plain,
% 2.22/2.40      ((~ (r1_tarski @ sk_C_1 @ 
% 2.22/2.40           (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 2.22/2.40        | ((sk_C_1) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 2.22/2.40      inference('sup-', [status(thm)], ['1', '2'])).
% 2.22/2.40  thf(commutativity_k2_tarski, axiom,
% 2.22/2.40    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.22/2.40  thf('4', plain,
% 2.22/2.40      (![X31 : $i, X32 : $i]:
% 2.22/2.40         ((k2_tarski @ X32 @ X31) = (k2_tarski @ X31 @ X32))),
% 2.22/2.40      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.22/2.40  thf(l51_zfmisc_1, axiom,
% 2.22/2.40    (![A:$i,B:$i]:
% 2.22/2.40     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.22/2.40  thf('5', plain,
% 2.22/2.40      (![X54 : $i, X55 : $i]:
% 2.22/2.40         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 2.22/2.40      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.22/2.40  thf('6', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 2.22/2.40      inference('sup+', [status(thm)], ['4', '5'])).
% 2.22/2.40  thf('7', plain,
% 2.22/2.40      (![X54 : $i, X55 : $i]:
% 2.22/2.40         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 2.22/2.40      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.22/2.40  thf('8', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.22/2.40      inference('sup+', [status(thm)], ['6', '7'])).
% 2.22/2.40  thf(t7_xboole_1, axiom,
% 2.22/2.40    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.22/2.40  thf('9', plain,
% 2.22/2.40      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 2.22/2.40      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.22/2.40  thf('10', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.22/2.40      inference('sup+', [status(thm)], ['6', '7'])).
% 2.22/2.40  thf('11', plain,
% 2.22/2.40      (((sk_C_1) = (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 2.22/2.40      inference('demod', [status(thm)], ['3', '8', '9', '10'])).
% 2.22/2.40  thf(t70_enumset1, axiom,
% 2.22/2.40    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.22/2.40  thf('12', plain,
% 2.22/2.40      (![X45 : $i, X46 : $i]:
% 2.22/2.40         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 2.22/2.40      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.22/2.40  thf(d1_enumset1, axiom,
% 2.22/2.40    (![A:$i,B:$i,C:$i,D:$i]:
% 2.22/2.40     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.22/2.40       ( ![E:$i]:
% 2.22/2.40         ( ( r2_hidden @ E @ D ) <=>
% 2.22/2.40           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.22/2.40  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.22/2.40  thf(zf_stmt_2, axiom,
% 2.22/2.40    (![E:$i,C:$i,B:$i,A:$i]:
% 2.22/2.40     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.22/2.40       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.22/2.40  thf(zf_stmt_3, axiom,
% 2.22/2.40    (![A:$i,B:$i,C:$i,D:$i]:
% 2.22/2.40     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.22/2.40       ( ![E:$i]:
% 2.22/2.40         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.22/2.40  thf('13', plain,
% 2.22/2.40      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.22/2.40         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41)
% 2.22/2.40          | (r2_hidden @ X38 @ X42)
% 2.22/2.40          | ((X42) != (k1_enumset1 @ X41 @ X40 @ X39)))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.22/2.40  thf('14', plain,
% 2.22/2.40      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.22/2.40         ((r2_hidden @ X38 @ (k1_enumset1 @ X41 @ X40 @ X39))
% 2.22/2.40          | (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41))),
% 2.22/2.40      inference('simplify', [status(thm)], ['13'])).
% 2.22/2.40  thf('15', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.40         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.22/2.40          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.22/2.40      inference('sup+', [status(thm)], ['12', '14'])).
% 2.22/2.40  thf('16', plain,
% 2.22/2.40      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.22/2.40         (((X34) != (X33)) | ~ (zip_tseitin_0 @ X34 @ X35 @ X36 @ X33))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.22/2.40  thf('17', plain,
% 2.22/2.40      (![X33 : $i, X35 : $i, X36 : $i]:
% 2.22/2.40         ~ (zip_tseitin_0 @ X33 @ X35 @ X36 @ X33)),
% 2.22/2.40      inference('simplify', [status(thm)], ['16'])).
% 2.22/2.40  thf('18', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.22/2.40      inference('sup-', [status(thm)], ['15', '17'])).
% 2.22/2.40  thf(d3_xboole_0, axiom,
% 2.22/2.40    (![A:$i,B:$i,C:$i]:
% 2.22/2.40     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.22/2.40       ( ![D:$i]:
% 2.22/2.40         ( ( r2_hidden @ D @ C ) <=>
% 2.22/2.40           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.22/2.40  thf('19', plain,
% 2.22/2.40      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.22/2.40         (~ (r2_hidden @ X2 @ X3)
% 2.22/2.40          | (r2_hidden @ X2 @ X4)
% 2.22/2.40          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.22/2.40      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.22/2.40  thf('20', plain,
% 2.22/2.40      (![X2 : $i, X3 : $i, X5 : $i]:
% 2.22/2.40         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 2.22/2.40      inference('simplify', [status(thm)], ['19'])).
% 2.22/2.40  thf('21', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.40         (r2_hidden @ X1 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 2.22/2.40      inference('sup-', [status(thm)], ['18', '20'])).
% 2.22/2.40  thf('22', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 2.22/2.40      inference('sup+', [status(thm)], ['11', '21'])).
% 2.22/2.40  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 2.22/2.40  
% 2.22/2.40  % SZS output end Refutation
% 2.22/2.40  
% 2.22/2.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
