%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xLDVE9h2Yu

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  54 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  316 ( 368 expanded)
%              Number of equality atoms :   42 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('0',plain,(
    ! [X37: $i,X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X37 @ X39 ) @ X40 )
        = ( k1_tarski @ X37 ) )
      | ( X37 != X39 )
      | ( r2_hidden @ X37 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r2_hidden @ X39 @ X40 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X39 @ X39 ) @ X40 )
        = ( k1_tarski @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r2_hidden @ X39 @ X40 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ X40 )
        = ( k1_tarski @ X39 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X41: $i,X42: $i] :
      ( r1_tarski @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('12',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44 != X43 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X43 ) )
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('13',plain,(
    ! [X43: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X43 ) )
     != ( k1_tarski @ X43 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X43: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X43 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(clc,[status(thm)],['11','19'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ( X14 = X13 )
      | ( X14 = X10 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('22',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X14 = X10 )
      | ( X14 = X13 )
      | ~ ( r2_hidden @ X14 @ ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xLDVE9h2Yu
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 79 iterations in 0.041s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(l38_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.50         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X37 : $i, X39 : $i, X40 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ (k2_tarski @ X37 @ X39) @ X40) = (k1_tarski @ X37))
% 0.21/0.50          | ((X37) != (X39))
% 0.21/0.50          | (r2_hidden @ X37 @ X40))),
% 0.21/0.50      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X39 : $i, X40 : $i]:
% 0.21/0.50         ((r2_hidden @ X39 @ X40)
% 0.21/0.50          | ((k4_xboole_0 @ (k2_tarski @ X39 @ X39) @ X40) = (k1_tarski @ X39)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.50  thf(t69_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('2', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X39 : $i, X40 : $i]:
% 0.21/0.50         ((r2_hidden @ X39 @ X40)
% 0.21/0.50          | ((k4_xboole_0 @ (k1_tarski @ X39) @ X40) = (k1_tarski @ X39)))),
% 0.21/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(t28_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.21/0.50          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.21/0.50             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t12_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X41 : $i, X42 : $i]:
% 0.21/0.50         (r1_tarski @ (k1_tarski @ X41) @ (k2_tarski @ X41 @ X42))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.50  thf(t1_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.50       ( r1_tarski @ A @ C ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.50          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.50          | (r1_tarski @ X3 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.21/0.50          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.50  thf(l32_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.21/0.50         = (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.50        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['3', '10'])).
% 0.21/0.50  thf(t20_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.50         ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ( A ) != ( B ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X43 : $i, X44 : $i]:
% 0.21/0.50         (((X44) != (X43))
% 0.21/0.50          | ((k4_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X43))
% 0.21/0.50              != (k1_tarski @ X44)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X43 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X43))
% 0.21/0.50           != (k1_tarski @ X43))),
% 0.21/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.50  thf(t3_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('14', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.50  thf(t48_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.21/0.50           = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf(t2_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.50  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain, (![X43 : $i]: ((k1_xboole_0) != (k1_tarski @ X43))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '18'])).
% 0.21/0.50  thf('20', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.21/0.50      inference('clc', [status(thm)], ['11', '19'])).
% 0.21/0.50  thf(d2_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X10 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X14 @ X12)
% 0.21/0.50          | ((X14) = (X13))
% 0.21/0.50          | ((X14) = (X10))
% 0.21/0.50          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X10 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (((X14) = (X10))
% 0.21/0.50          | ((X14) = (X13))
% 0.21/0.50          | ~ (r2_hidden @ X14 @ (k2_tarski @ X13 @ X10)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.50  thf('23', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_D_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.50  thf('24', plain, (((sk_A) != (sk_D_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain, (((sk_A) != (sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
