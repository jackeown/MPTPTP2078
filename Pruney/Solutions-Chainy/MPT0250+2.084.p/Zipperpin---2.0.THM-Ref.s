%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4JQnj6AO6G

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:58 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  258 ( 377 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
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

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
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
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X72: $i,X73: $i] :
      ( ( r1_tarski @ X72 @ ( k3_tarski @ X73 ) )
      | ~ ( r2_hidden @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X74 @ X75 ) )
      = ( k2_xboole_0 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4JQnj6AO6G
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.69  % Solved by: fo/fo7.sh
% 0.50/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.69  % done 285 iterations in 0.215s
% 0.50/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.69  % SZS output start Refutation
% 0.50/0.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.50/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.50/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.69  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.50/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.50/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.69  thf(t45_zfmisc_1, conjecture,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.50/0.69       ( r2_hidden @ A @ B ) ))).
% 0.50/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.69    (~( ![A:$i,B:$i]:
% 0.50/0.69        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.50/0.69          ( r2_hidden @ A @ B ) ) )),
% 0.50/0.69    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.50/0.69  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(t69_enumset1, axiom,
% 0.50/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.50/0.69  thf('1', plain, (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 0.50/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.69  thf(t70_enumset1, axiom,
% 0.50/0.69    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.50/0.69  thf('2', plain,
% 0.50/0.69      (![X45 : $i, X46 : $i]:
% 0.50/0.69         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.50/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.50/0.69  thf(d1_enumset1, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.69     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.50/0.69       ( ![E:$i]:
% 0.50/0.69         ( ( r2_hidden @ E @ D ) <=>
% 0.50/0.69           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.50/0.69  thf(zf_stmt_2, axiom,
% 0.50/0.69    (![E:$i,C:$i,B:$i,A:$i]:
% 0.50/0.69     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.50/0.69       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_3, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.69     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.50/0.69       ( ![E:$i]:
% 0.50/0.69         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.50/0.69  thf('3', plain,
% 0.50/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.69         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.50/0.69          | (r2_hidden @ X14 @ X18)
% 0.50/0.69          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('4', plain,
% 0.50/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.69         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.50/0.69          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.50/0.69      inference('simplify', [status(thm)], ['3'])).
% 0.50/0.69  thf('5', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.50/0.69          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.50/0.69      inference('sup+', [status(thm)], ['2', '4'])).
% 0.50/0.69  thf('6', plain,
% 0.50/0.69      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.50/0.69         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.50/0.69  thf('7', plain,
% 0.50/0.69      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.50/0.69      inference('simplify', [status(thm)], ['6'])).
% 0.50/0.69  thf('8', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.50/0.69      inference('sup-', [status(thm)], ['5', '7'])).
% 0.50/0.69  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['1', '8'])).
% 0.50/0.69  thf('10', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.50/0.69      inference('sup-', [status(thm)], ['5', '7'])).
% 0.50/0.69  thf(l49_zfmisc_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.50/0.69  thf('11', plain,
% 0.50/0.69      (![X72 : $i, X73 : $i]:
% 0.50/0.69         ((r1_tarski @ X72 @ (k3_tarski @ X73)) | ~ (r2_hidden @ X72 @ X73))),
% 0.50/0.69      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.50/0.69  thf('12', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.50/0.69  thf(l51_zfmisc_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.69  thf('13', plain,
% 0.50/0.69      (![X74 : $i, X75 : $i]:
% 0.50/0.69         ((k3_tarski @ (k2_tarski @ X74 @ X75)) = (k2_xboole_0 @ X74 @ X75))),
% 0.50/0.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.50/0.69  thf('14', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.50/0.69      inference('demod', [status(thm)], ['12', '13'])).
% 0.50/0.69  thf(d3_tarski, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.50/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.50/0.69  thf('15', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.69          | (r2_hidden @ X0 @ X2)
% 0.50/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.50/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.69  thf('16', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.50/0.69      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.69  thf('17', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.50/0.69      inference('sup-', [status(thm)], ['9', '16'])).
% 0.50/0.69  thf('18', plain,
% 0.50/0.69      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('19', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.69          | (r2_hidden @ X0 @ X2)
% 0.50/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.50/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.69  thf('20', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((r2_hidden @ X0 @ sk_B)
% 0.50/0.69          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.69  thf('21', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.50/0.69      inference('sup-', [status(thm)], ['17', '20'])).
% 0.50/0.69  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.50/0.69  
% 0.50/0.69  % SZS output end Refutation
% 0.50/0.69  
% 0.50/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
