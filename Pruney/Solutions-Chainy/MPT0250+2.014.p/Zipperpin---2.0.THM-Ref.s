%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9NotWK5Ich

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:49 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   57 (  75 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  352 ( 491 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
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

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('20',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['9','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9NotWK5Ich
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 266 iterations in 0.132s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(t45_zfmisc_1, conjecture,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.37/0.59       ( r2_hidden @ A @ B ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i]:
% 0.37/0.59        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.37/0.59          ( r2_hidden @ A @ B ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.37/0.59  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t69_enumset1, axiom,
% 0.37/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.59  thf('1', plain, (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.37/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.59  thf(t70_enumset1, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X28 : $i, X29 : $i]:
% 0.37/0.59         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.37/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.59  thf(d1_enumset1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.59       ( ![E:$i]:
% 0.37/0.59         ( ( r2_hidden @ E @ D ) <=>
% 0.37/0.59           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.37/0.59  thf(zf_stmt_2, axiom,
% 0.37/0.59    (![E:$i,C:$i,B:$i,A:$i]:
% 0.37/0.59     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.37/0.59       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_3, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.59       ( ![E:$i]:
% 0.37/0.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.59         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.37/0.59          | (r2_hidden @ X20 @ X24)
% 0.37/0.59          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.59         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 0.37/0.59          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.37/0.59      inference('simplify', [status(thm)], ['3'])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.37/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['2', '4'])).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.59         (((X16) != (X15)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.37/0.59         ~ (zip_tseitin_0 @ X15 @ X17 @ X18 @ X15)),
% 0.37/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['5', '7'])).
% 0.37/0.59  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['1', '8'])).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(d10_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      (![X6 : $i, X8 : $i]:
% 0.37/0.59         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.37/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.37/0.59        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.59  thf(commutativity_k2_tarski, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      (![X13 : $i, X14 : $i]:
% 0.37/0.59         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.37/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.59  thf(l51_zfmisc_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      (![X39 : $i, X40 : $i]:
% 0.37/0.59         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.37/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      (![X39 : $i, X40 : $i]:
% 0.37/0.59         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.37/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.59  thf(t7_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.59  thf('20', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['12', '17', '18', '19'])).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.59  thf('22', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.59  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.37/0.59      inference('sup+', [status(thm)], ['20', '23'])).
% 0.37/0.59  thf(t28_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i]:
% 0.37/0.59         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.59  thf('26', plain,
% 0.37/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.59  thf(d4_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.59       ( ![D:$i]:
% 0.37/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.59           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.59          | (r2_hidden @ X4 @ X2)
% 0.37/0.59          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.59         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.59  thf('29', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | (r2_hidden @ X0 @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['26', '28'])).
% 0.37/0.59  thf('30', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.37/0.59      inference('sup-', [status(thm)], ['9', '29'])).
% 0.37/0.59  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
