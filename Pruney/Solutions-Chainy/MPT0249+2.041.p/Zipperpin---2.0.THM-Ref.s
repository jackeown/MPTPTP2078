%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0djXZN0Xby

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:44 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 184 expanded)
%              Number of leaves         :   25 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  464 (1538 expanded)
%              Number of equality atoms :   66 ( 288 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X52
        = ( k1_tarski @ X51 ) )
      | ( X52 = k1_xboole_0 )
      | ~ ( r1_tarski @ X52 @ ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('5',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('19',plain,(
    r2_hidden @ ( sk_B @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( X12 = X13 )
      | ( X12 = X14 )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_B @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X56: $i,X58: $i,X59: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X56 @ X58 ) @ X59 )
      | ~ ( r2_hidden @ X58 @ X59 )
      | ~ ( r2_hidden @ X56 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ ( sk_B @ sk_C ) @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','37'])).

thf('39',plain,
    ( ( sk_B @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['19','30'])).

thf('40',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('42',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_B_1 = sk_C ),
    inference('sup+',[status(thm)],['8','46'])).

thf('48',plain,(
    sk_B_1 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0djXZN0Xby
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:02:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 556 iterations in 0.157s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.60  thf(t44_zfmisc_1, conjecture,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.38/0.60          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.38/0.60          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.60        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.38/0.60             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.38/0.60             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.38/0.60  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t7_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.60  thf('3', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.38/0.60      inference('sup+', [status(thm)], ['1', '2'])).
% 0.38/0.60  thf(l3_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.38/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X51 : $i, X52 : $i]:
% 0.38/0.60         (((X52) = (k1_tarski @ X51))
% 0.38/0.60          | ((X52) = (k1_xboole_0))
% 0.38/0.60          | ~ (r1_tarski @ X52 @ (k1_tarski @ X51)))),
% 0.38/0.60      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.60  thf('6', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('7', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.38/0.60  thf('8', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.38/0.60      inference('demod', [status(thm)], ['0', '7'])).
% 0.38/0.60  thf(t7_xboole_0, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.60  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.60  thf(d3_xboole_0, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.38/0.60       ( ![D:$i]:
% 0.38/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.60           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.60          | (r2_hidden @ X0 @ X2)
% 0.38/0.60          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.38/0.60         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (((X0) = (k1_xboole_0))
% 0.38/0.60          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (((r2_hidden @ (sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.38/0.60        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['10', '14'])).
% 0.38/0.60  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('17', plain, ((r2_hidden @ (sk_B @ sk_C) @ (k1_tarski @ sk_A))),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('18', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.38/0.60  thf('19', plain, ((r2_hidden @ (sk_B @ sk_C) @ sk_B_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.60  thf(d1_enumset1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.60       ( ![E:$i]:
% 0.38/0.60         ( ( r2_hidden @ E @ D ) <=>
% 0.38/0.60           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_1, axiom,
% 0.38/0.60    (![E:$i,C:$i,B:$i,A:$i]:
% 0.38/0.60     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.38/0.60       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.38/0.60          | ((X12) = (X13))
% 0.38/0.60          | ((X12) = (X14))
% 0.38/0.60          | ((X12) = (X15)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.60  thf('21', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.38/0.60  thf(t70_enumset1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      (![X24 : $i, X25 : $i]:
% 0.38/0.60         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.38/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.60  thf(t69_enumset1, axiom,
% 0.38/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.38/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.38/0.60      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.60  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_3, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.60       ( ![E:$i]:
% 0.38/0.60         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X21 @ X20)
% 0.38/0.60          | ~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.38/0.60          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.38/0.60         (~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.38/0.60          | ~ (r2_hidden @ X21 @ (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.38/0.60          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['24', '26'])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.38/0.60          | ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['21', '27'])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (sk_A))
% 0.38/0.60          | ((X0) = (sk_A))
% 0.38/0.60          | ((X0) = (sk_A))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['20', '28'])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['29'])).
% 0.38/0.60  thf('31', plain, (((sk_B @ sk_C) = (sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['19', '30'])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.60  thf('33', plain, (((r2_hidden @ sk_A @ sk_C) | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['31', '32'])).
% 0.38/0.60  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('35', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.38/0.60  thf(t38_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.38/0.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      (![X56 : $i, X58 : $i, X59 : $i]:
% 0.38/0.60         ((r1_tarski @ (k2_tarski @ X56 @ X58) @ X59)
% 0.38/0.60          | ~ (r2_hidden @ X58 @ X59)
% 0.38/0.60          | ~ (r2_hidden @ X56 @ X59))),
% 0.38/0.60      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X0 @ sk_C)
% 0.38/0.60          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      ((((sk_C) = (k1_xboole_0))
% 0.38/0.60        | (r1_tarski @ (k2_tarski @ (sk_B @ sk_C) @ sk_A) @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['9', '37'])).
% 0.38/0.60  thf('39', plain, (((sk_B @ sk_C) = (sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['19', '30'])).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.38/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.60  thf('41', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.38/0.60  thf('42', plain, ((((sk_C) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C))),
% 0.38/0.60      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.38/0.60  thf('43', plain, (((sk_C) != (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('44', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.38/0.60  thf(t12_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      (![X7 : $i, X8 : $i]:
% 0.38/0.60         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.38/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.60  thf('46', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C) = (sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.60  thf('47', plain, (((sk_B_1) = (sk_C))),
% 0.38/0.60      inference('sup+', [status(thm)], ['8', '46'])).
% 0.38/0.60  thf('48', plain, (((sk_B_1) != (sk_C))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('49', plain, ($false),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
