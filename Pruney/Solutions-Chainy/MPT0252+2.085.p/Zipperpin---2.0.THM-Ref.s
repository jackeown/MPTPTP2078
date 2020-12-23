%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d8z59Oc8M2

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:27 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   57 (  74 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  385 ( 562 expanded)
%              Number of equality atoms :   22 (  37 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
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

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('10',plain,
    ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = sk_C_1 )
    | ( r2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X72: $i,X73: $i] :
      ( ( r1_tarski @ X72 @ ( k3_tarski @ X73 ) )
      | ~ ( r2_hidden @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ( r1_tarski @ X3 @ ( k3_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r2_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( r2_xboole_0 @ ( k3_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X74 @ X75 ) )
      = ( k2_xboole_0 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = sk_C_1 )
    | ( zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X11 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = sk_C_1 ),
    inference(clc,[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('25',plain,(
    ! [X72: $i,X73: $i] :
      ( ( r1_tarski @ X72 @ ( k3_tarski @ X73 ) )
      | ~ ( r2_hidden @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X74 @ X75 ) )
      = ( k2_xboole_0 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference('sup+',[status(thm)],['23','28'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d8z59Oc8M2
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 289 iterations in 0.185s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.63  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.45/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(t47_zfmisc_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.45/0.63       ( r2_hidden @ A @ C ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.63        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.45/0.63          ( r2_hidden @ A @ C ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.45/0.63  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t70_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X45 : $i, X46 : $i]:
% 0.45/0.63         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.45/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.63  thf(d1_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.63       ( ![E:$i]:
% 0.45/0.63         ( ( r2_hidden @ E @ D ) <=>
% 0.45/0.63           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.63  thf(zf_stmt_2, axiom,
% 0.45/0.63    (![E:$i,C:$i,B:$i,A:$i]:
% 0.45/0.63     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.45/0.63       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_3, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.63       ( ![E:$i]:
% 0.45/0.63         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.63         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.45/0.63          | (r2_hidden @ X14 @ X18)
% 0.45/0.63          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.63         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.45/0.63          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.45/0.63      inference('simplify', [status(thm)], ['2'])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.63          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.63      inference('sup+', [status(thm)], ['1', '3'])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.63         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.45/0.63      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d8_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.45/0.63       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X4 : $i, X6 : $i]:
% 0.45/0.63         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.45/0.63      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      ((((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1))
% 0.45/0.63        | (r2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ 
% 0.45/0.63           sk_C_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X45 : $i, X46 : $i]:
% 0.45/0.63         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.45/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.63         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.45/0.63          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.45/0.63      inference('simplify', [status(thm)], ['2'])).
% 0.45/0.63  thf(l49_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (![X72 : $i, X73 : $i]:
% 0.45/0.63         ((r1_tarski @ X72 @ (k3_tarski @ X73)) | ~ (r2_hidden @ X72 @ X73))),
% 0.45/0.63      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.45/0.63          | (r1_tarski @ X3 @ (k3_tarski @ (k1_enumset1 @ X2 @ X1 @ X0))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.63  thf(t60_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X7 : $i, X8 : $i]:
% 0.45/0.63         (~ (r1_tarski @ X7 @ X8) | ~ (r2_xboole_0 @ X8 @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.45/0.63          | ~ (r2_xboole_0 @ (k3_tarski @ (k1_enumset1 @ X2 @ X1 @ X0)) @ X3))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2)
% 0.45/0.63          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '16'])).
% 0.45/0.63  thf(l51_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (![X74 : $i, X75 : $i]:
% 0.45/0.63         ((k3_tarski @ (k2_tarski @ X74 @ X75)) = (k2_xboole_0 @ X74 @ X75))),
% 0.45/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.63          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      ((((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1))
% 0.45/0.63        | (zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63           (k2_tarski @ sk_A @ sk_B)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.63         (((X10) != (X11)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X11 @ X11 @ X12 @ X9)),
% 0.45/0.63      inference('simplify', [status(thm)], ['21'])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1))),
% 0.45/0.63      inference('clc', [status(thm)], ['20', '22'])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (![X72 : $i, X73 : $i]:
% 0.45/0.63         ((r1_tarski @ X72 @ (k3_tarski @ X73)) | ~ (r2_hidden @ X72 @ X73))),
% 0.45/0.63      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (![X74 : $i, X75 : $i]:
% 0.45/0.63         ((k3_tarski @ (k2_tarski @ X74 @ X75)) = (k2_xboole_0 @ X74 @ X75))),
% 0.45/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.63  thf('29', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.45/0.63      inference('sup+', [status(thm)], ['23', '28'])).
% 0.45/0.63  thf(d3_tarski, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.63          | (r2_hidden @ X0 @ X2)
% 0.45/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((r2_hidden @ X0 @ sk_C_1)
% 0.45/0.63          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.63  thf('32', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['7', '31'])).
% 0.45/0.63  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
