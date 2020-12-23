%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tpZntso5pp

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:49 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   64 (  74 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  424 ( 504 expanded)
%              Number of equality atoms :   34 (  42 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('23',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','20','21','22'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ X18 )
      | ( ( k4_xboole_0 @ X16 @ X18 )
       != X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_B )
       != ( k4_xboole_0 @ X0 @ sk_B ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('31',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X43 ) @ X44 )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tpZntso5pp
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 620 iterations in 0.413s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.69/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.69/0.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.69/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.88  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.69/0.88  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.69/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.88  thf(t45_zfmisc_1, conjecture,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.69/0.88       ( r2_hidden @ A @ B ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ![A:$i,B:$i]:
% 0.69/0.88        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.69/0.88          ( r2_hidden @ A @ B ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.69/0.88  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(t69_enumset1, axiom,
% 0.69/0.88    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.69/0.88  thf('1', plain, (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.69/0.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.88  thf(t70_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.69/0.88  thf('2', plain,
% 0.69/0.88      (![X34 : $i, X35 : $i]:
% 0.69/0.88         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.69/0.88      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.69/0.88  thf(d1_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.69/0.88       ( ![E:$i]:
% 0.69/0.88         ( ( r2_hidden @ E @ D ) <=>
% 0.69/0.88           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.69/0.88  thf(zf_stmt_2, axiom,
% 0.69/0.88    (![E:$i,C:$i,B:$i,A:$i]:
% 0.69/0.88     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.69/0.88       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_3, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.69/0.88       ( ![E:$i]:
% 0.69/0.88         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.69/0.88  thf('3', plain,
% 0.69/0.88      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.88         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 0.69/0.88          | (r2_hidden @ X26 @ X30)
% 0.69/0.88          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.69/0.88  thf('4', plain,
% 0.69/0.88      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.69/0.88         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 0.69/0.88          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 0.69/0.88      inference('simplify', [status(thm)], ['3'])).
% 0.69/0.88  thf('5', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.69/0.88          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['2', '4'])).
% 0.69/0.88  thf('6', plain,
% 0.69/0.88      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.69/0.88         (((X22) != (X21)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.69/0.88  thf('7', plain,
% 0.69/0.88      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.69/0.88         ~ (zip_tseitin_0 @ X21 @ X23 @ X24 @ X21)),
% 0.69/0.88      inference('simplify', [status(thm)], ['6'])).
% 0.69/0.88  thf('8', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.69/0.88      inference('sup-', [status(thm)], ['5', '7'])).
% 0.69/0.88  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['1', '8'])).
% 0.69/0.88  thf(d5_xboole_0, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.69/0.88       ( ![D:$i]:
% 0.69/0.88         ( ( r2_hidden @ D @ C ) <=>
% 0.69/0.88           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.69/0.88  thf('10', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.69/0.88          | (r2_hidden @ X0 @ X2)
% 0.69/0.88          | (r2_hidden @ X0 @ X3)
% 0.69/0.88          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.69/0.88      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.88  thf('11', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.69/0.88          | (r2_hidden @ X0 @ X2)
% 0.69/0.88          | ~ (r2_hidden @ X0 @ X1))),
% 0.69/0.88      inference('simplify', [status(thm)], ['10'])).
% 0.69/0.88  thf('12', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((r2_hidden @ X0 @ X1)
% 0.69/0.88          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['9', '11'])).
% 0.69/0.88  thf('13', plain,
% 0.69/0.88      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(d10_xboole_0, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.88  thf('14', plain,
% 0.69/0.88      (![X8 : $i, X10 : $i]:
% 0.69/0.88         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.69/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.88  thf('15', plain,
% 0.69/0.88      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.69/0.88        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['13', '14'])).
% 0.69/0.88  thf(commutativity_k2_tarski, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.69/0.88  thf('16', plain,
% 0.69/0.88      (![X19 : $i, X20 : $i]:
% 0.69/0.88         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.69/0.88      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.69/0.88  thf(l51_zfmisc_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.88  thf('17', plain,
% 0.69/0.88      (![X45 : $i, X46 : $i]:
% 0.69/0.88         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.69/0.88      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.88  thf('18', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['16', '17'])).
% 0.69/0.88  thf('19', plain,
% 0.69/0.88      (![X45 : $i, X46 : $i]:
% 0.69/0.88         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.69/0.88      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.88  thf('20', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['18', '19'])).
% 0.69/0.88  thf(t7_xboole_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.88  thf('21', plain,
% 0.69/0.88      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.69/0.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.69/0.88  thf('22', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['18', '19'])).
% 0.69/0.88  thf('23', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.69/0.88      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 0.69/0.88  thf(t41_xboole_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.69/0.88       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.69/0.88  thf('24', plain,
% 0.69/0.88      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.69/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.69/0.88           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.69/0.88  thf(t83_xboole_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.69/0.88  thf('25', plain,
% 0.69/0.88      (![X16 : $i, X18 : $i]:
% 0.69/0.88         ((r1_xboole_0 @ X16 @ X18) | ((k4_xboole_0 @ X16 @ X18) != (X16)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.69/0.88  thf('26', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.69/0.88            != (k4_xboole_0 @ X2 @ X1))
% 0.69/0.88          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.88  thf('27', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k4_xboole_0 @ X0 @ sk_B) != (k4_xboole_0 @ X0 @ sk_B))
% 0.69/0.88          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['23', '26'])).
% 0.69/0.88  thf('28', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_A))),
% 0.69/0.88      inference('simplify', [status(thm)], ['27'])).
% 0.69/0.88  thf(symmetry_r1_xboole_0, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.69/0.88  thf('29', plain,
% 0.69/0.88      (![X6 : $i, X7 : $i]:
% 0.69/0.88         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.69/0.88      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.69/0.88  thf('30', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['28', '29'])).
% 0.69/0.88  thf(l24_zfmisc_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.69/0.88  thf('31', plain,
% 0.69/0.88      (![X43 : $i, X44 : $i]:
% 0.69/0.88         (~ (r1_xboole_0 @ (k1_tarski @ X43) @ X44) | ~ (r2_hidden @ X43 @ X44))),
% 0.69/0.88      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.69/0.88  thf('32', plain,
% 0.69/0.88      (![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('33', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.69/0.88      inference('sup-', [status(thm)], ['12', '32'])).
% 0.69/0.88  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
