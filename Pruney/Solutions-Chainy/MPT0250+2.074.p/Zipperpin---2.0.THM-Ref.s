%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xzUcUBCqg8

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:57 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  327 ( 521 expanded)
%              Number of equality atoms :   22 (  38 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X12 @ X16 )
      | ( X16
       != ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X9 @ X10 @ X7 ) ),
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
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X9 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('17',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ X53 @ ( k3_tarski @ X54 ) )
      | ~ ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('23',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ X53 @ ( k3_tarski @ X54 ) )
      | ~ ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['21','26'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['9','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xzUcUBCqg8
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.13/2.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.13/2.33  % Solved by: fo/fo7.sh
% 2.13/2.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.13/2.33  % done 558 iterations in 1.877s
% 2.13/2.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.13/2.33  % SZS output start Refutation
% 2.13/2.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.13/2.33  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.13/2.33  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.13/2.33  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.13/2.33  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.13/2.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.13/2.33  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.13/2.33  thf(sk_B_type, type, sk_B: $i).
% 2.13/2.33  thf(sk_A_type, type, sk_A: $i).
% 2.13/2.33  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.13/2.33  thf(t45_zfmisc_1, conjecture,
% 2.13/2.33    (![A:$i,B:$i]:
% 2.13/2.33     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 2.13/2.33       ( r2_hidden @ A @ B ) ))).
% 2.13/2.33  thf(zf_stmt_0, negated_conjecture,
% 2.13/2.33    (~( ![A:$i,B:$i]:
% 2.13/2.33        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 2.13/2.33          ( r2_hidden @ A @ B ) ) )),
% 2.13/2.33    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 2.13/2.33  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf(t69_enumset1, axiom,
% 2.13/2.33    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.13/2.33  thf('1', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 2.13/2.33      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.13/2.33  thf(t70_enumset1, axiom,
% 2.13/2.33    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.13/2.33  thf('2', plain,
% 2.13/2.33      (![X20 : $i, X21 : $i]:
% 2.13/2.33         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 2.13/2.33      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.13/2.33  thf(d1_enumset1, axiom,
% 2.13/2.33    (![A:$i,B:$i,C:$i,D:$i]:
% 2.13/2.33     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.13/2.33       ( ![E:$i]:
% 2.13/2.33         ( ( r2_hidden @ E @ D ) <=>
% 2.13/2.33           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.13/2.33  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.13/2.33  thf(zf_stmt_2, axiom,
% 2.13/2.33    (![E:$i,C:$i,B:$i,A:$i]:
% 2.13/2.33     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.13/2.33       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.13/2.33  thf(zf_stmt_3, axiom,
% 2.13/2.33    (![A:$i,B:$i,C:$i,D:$i]:
% 2.13/2.33     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.13/2.33       ( ![E:$i]:
% 2.13/2.33         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.13/2.33  thf('3', plain,
% 2.13/2.33      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.13/2.33         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 2.13/2.33          | (r2_hidden @ X12 @ X16)
% 2.13/2.33          | ((X16) != (k1_enumset1 @ X15 @ X14 @ X13)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.13/2.33  thf('4', plain,
% 2.13/2.33      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.13/2.33         ((r2_hidden @ X12 @ (k1_enumset1 @ X15 @ X14 @ X13))
% 2.13/2.33          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 2.13/2.33      inference('simplify', [status(thm)], ['3'])).
% 2.13/2.33  thf('5', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.33         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.13/2.33          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.13/2.33      inference('sup+', [status(thm)], ['2', '4'])).
% 2.13/2.33  thf('6', plain,
% 2.13/2.33      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.13/2.33         (((X8) != (X7)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.13/2.33  thf('7', plain,
% 2.13/2.33      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X7 @ X9 @ X10 @ X7)),
% 2.13/2.33      inference('simplify', [status(thm)], ['6'])).
% 2.13/2.33  thf('8', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.13/2.33      inference('sup-', [status(thm)], ['5', '7'])).
% 2.13/2.33  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.13/2.33      inference('sup+', [status(thm)], ['1', '8'])).
% 2.13/2.33  thf('10', plain,
% 2.13/2.33      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf(d10_xboole_0, axiom,
% 2.13/2.33    (![A:$i,B:$i]:
% 2.13/2.33     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.13/2.33  thf('11', plain,
% 2.13/2.33      (![X4 : $i, X6 : $i]:
% 2.13/2.33         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 2.13/2.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.13/2.33  thf('12', plain,
% 2.13/2.33      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 2.13/2.33        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['10', '11'])).
% 2.13/2.33  thf('13', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.33         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.13/2.33          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.13/2.33      inference('sup+', [status(thm)], ['2', '4'])).
% 2.13/2.33  thf('14', plain,
% 2.13/2.33      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.13/2.33         (((X8) != (X9)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.13/2.33  thf('15', plain,
% 2.13/2.33      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X9 @ X9 @ X10 @ X7)),
% 2.13/2.33      inference('simplify', [status(thm)], ['14'])).
% 2.13/2.33  thf('16', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 2.13/2.33      inference('sup-', [status(thm)], ['13', '15'])).
% 2.13/2.33  thf(l49_zfmisc_1, axiom,
% 2.13/2.33    (![A:$i,B:$i]:
% 2.13/2.33     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 2.13/2.33  thf('17', plain,
% 2.13/2.33      (![X53 : $i, X54 : $i]:
% 2.13/2.33         ((r1_tarski @ X53 @ (k3_tarski @ X54)) | ~ (r2_hidden @ X53 @ X54))),
% 2.13/2.33      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 2.13/2.33  thf('18', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]:
% 2.13/2.33         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['16', '17'])).
% 2.13/2.33  thf(l51_zfmisc_1, axiom,
% 2.13/2.33    (![A:$i,B:$i]:
% 2.13/2.33     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.13/2.33  thf('19', plain,
% 2.13/2.33      (![X55 : $i, X56 : $i]:
% 2.13/2.33         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 2.13/2.33      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.13/2.33  thf('20', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.13/2.33      inference('demod', [status(thm)], ['18', '19'])).
% 2.13/2.33  thf('21', plain, (((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 2.13/2.33      inference('demod', [status(thm)], ['12', '20'])).
% 2.13/2.33  thf('22', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.13/2.33      inference('sup-', [status(thm)], ['5', '7'])).
% 2.13/2.33  thf('23', plain,
% 2.13/2.33      (![X53 : $i, X54 : $i]:
% 2.13/2.33         ((r1_tarski @ X53 @ (k3_tarski @ X54)) | ~ (r2_hidden @ X53 @ X54))),
% 2.13/2.33      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 2.13/2.33  thf('24', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]:
% 2.13/2.33         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['22', '23'])).
% 2.13/2.33  thf('25', plain,
% 2.13/2.33      (![X55 : $i, X56 : $i]:
% 2.13/2.33         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 2.13/2.33      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.13/2.33  thf('26', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 2.13/2.33      inference('demod', [status(thm)], ['24', '25'])).
% 2.13/2.33  thf('27', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 2.13/2.33      inference('sup+', [status(thm)], ['21', '26'])).
% 2.13/2.33  thf(d3_tarski, axiom,
% 2.13/2.33    (![A:$i,B:$i]:
% 2.13/2.33     ( ( r1_tarski @ A @ B ) <=>
% 2.13/2.33       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.13/2.33  thf('28', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.33         (~ (r2_hidden @ X0 @ X1)
% 2.13/2.33          | (r2_hidden @ X0 @ X2)
% 2.13/2.33          | ~ (r1_tarski @ X1 @ X2))),
% 2.13/2.33      inference('cnf', [status(esa)], [d3_tarski])).
% 2.13/2.33  thf('29', plain,
% 2.13/2.33      (![X0 : $i]:
% 2.13/2.33         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['27', '28'])).
% 2.13/2.33  thf('30', plain, ((r2_hidden @ sk_A @ sk_B)),
% 2.13/2.33      inference('sup-', [status(thm)], ['9', '29'])).
% 2.13/2.33  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 2.13/2.33  
% 2.13/2.33  % SZS output end Refutation
% 2.13/2.33  
% 2.13/2.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
