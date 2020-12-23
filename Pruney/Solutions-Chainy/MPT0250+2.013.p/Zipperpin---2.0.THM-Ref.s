%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Xb0EYrbdl

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  59 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  307 ( 387 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','8','9','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
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

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['11','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Xb0EYrbdl
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 190 iterations in 0.106s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.56  thf(t45_zfmisc_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.21/0.56       ( r2_hidden @ A @ B ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i]:
% 0.21/0.56        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.21/0.56          ( r2_hidden @ A @ B ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.21/0.56  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d10_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X6 : $i, X8 : $i]:
% 0.21/0.56         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.21/0.56        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf(commutativity_k2_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.56  thf(l51_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X53 : $i, X54 : $i]:
% 0.21/0.56         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.21/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X53 : $i, X54 : $i]:
% 0.21/0.56         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.21/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf(t7_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('11', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '8', '9', '10'])).
% 0.21/0.56  thf(t69_enumset1, axiom,
% 0.21/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.56  thf(t70_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X26 : $i, X27 : $i]:
% 0.21/0.56         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.21/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.56  thf(d1_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.56       ( ![E:$i]:
% 0.21/0.56         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.56           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_2, axiom,
% 0.21/0.56    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.56     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.56       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_3, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.56       ( ![E:$i]:
% 0.21/0.56         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.21/0.56          | (r2_hidden @ X18 @ X22)
% 0.21/0.56          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.56         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.21/0.56          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.21/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.56          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.56      inference('sup+', [status(thm)], ['13', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.56  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['12', '19'])).
% 0.21/0.56  thf(d3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.56           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.56          | (r2_hidden @ X0 @ X2)
% 0.21/0.56          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.21/0.56         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.56  thf('24', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.56      inference('sup+', [status(thm)], ['11', '23'])).
% 0.21/0.56  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
