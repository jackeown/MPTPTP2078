%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yDxi0sk98X

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:31 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  445 ( 602 expanded)
%              Number of equality atoms :   44 (  65 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ ( k1_tarski @ X15 ) )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('1',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ ( sk_D @ X5 @ X4 @ X3 ) @ X5 )
      | ( X3
        = ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r1_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) @ X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) @ ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k1_tarski @ X13 ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('9',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ ( sk_D @ X5 @ X4 @ X3 ) @ X4 )
      | ( X3
        = ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r1_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) @ ( k1_tarski @ X0 ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) @ ( k1_tarski @ X1 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ~ ( r1_tarski @ ( sk_D @ X5 @ X4 @ X3 ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X1 ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('22',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['16','20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17 = X16 )
      | ~ ( r1_tarski @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t17_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != B )
       => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_zfmisc_1])).

thf('30',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yDxi0sk98X
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 165 iterations in 0.095s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(l3_zfmisc_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.38/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      (![X14 : $i, X15 : $i]:
% 0.38/0.55         ((r1_tarski @ X14 @ (k1_tarski @ X15)) | ((X14) != (k1_xboole_0)))),
% 0.38/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.38/0.55  thf('1', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.55  thf('2', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.55  thf(t20_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.38/0.55         ( ![D:$i]:
% 0.38/0.55           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.38/0.55             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.38/0.55       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X3 @ X4)
% 0.38/0.55          | ~ (r1_tarski @ X3 @ X5)
% 0.38/0.55          | (r1_tarski @ (sk_D @ X5 @ X4 @ X3) @ X5)
% 0.38/0.55          | ((X3) = (k3_xboole_0 @ X4 @ X5)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.38/0.55          | (r1_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ k1_xboole_0) @ X1)
% 0.38/0.55          | ~ (r1_tarski @ k1_xboole_0 @ X1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((r1_tarski @ 
% 0.38/0.55           (sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0) @ 
% 0.38/0.55           (k1_tarski @ X0))
% 0.38/0.55          | ((k1_xboole_0)
% 0.38/0.55              = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['1', '4'])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i]:
% 0.38/0.55         (((X14) = (k1_tarski @ X13))
% 0.38/0.55          | ((X14) = (k1_xboole_0))
% 0.38/0.55          | ~ (r1_tarski @ X14 @ (k1_tarski @ X13)))),
% 0.38/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.38/0.55          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0)
% 0.38/0.55              = (k1_xboole_0))
% 0.38/0.55          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0)
% 0.38/0.55              = (k1_tarski @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.55  thf('8', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.55  thf('9', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X3 @ X4)
% 0.38/0.55          | ~ (r1_tarski @ X3 @ X5)
% 0.38/0.55          | (r1_tarski @ (sk_D @ X5 @ X4 @ X3) @ X4)
% 0.38/0.55          | ((X3) = (k3_xboole_0 @ X4 @ X5)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.38/0.55          | (r1_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ k1_xboole_0) @ 
% 0.38/0.55             (k1_tarski @ X0))
% 0.38/0.55          | ~ (r1_tarski @ k1_xboole_0 @ X1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((r1_tarski @ 
% 0.38/0.55           (sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0) @ 
% 0.38/0.55           (k1_tarski @ X1))
% 0.38/0.55          | ((k1_xboole_0)
% 0.38/0.55              = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['8', '11'])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.38/0.55          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0)
% 0.38/0.55              = (k1_xboole_0))
% 0.38/0.55          | ((k1_xboole_0)
% 0.38/0.55              = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.38/0.55          | ((k1_xboole_0)
% 0.38/0.55              = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['7', '12'])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.38/0.55          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0)
% 0.38/0.55              = (k1_xboole_0))
% 0.38/0.55          | (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X3 @ X4)
% 0.38/0.55          | ~ (r1_tarski @ X3 @ X5)
% 0.38/0.55          | ~ (r1_tarski @ (sk_D @ X5 @ X4 @ X3) @ X3)
% 0.38/0.55          | ((X3) = (k3_xboole_0 @ X4 @ X5)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.38/0.55          | (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.38/0.55          | ((k1_xboole_0)
% 0.38/0.55              = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.38/0.55          | ((k1_xboole_0)
% 0.38/0.55              = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.38/0.55          | ~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X1))
% 0.38/0.55          | ~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.55  thf(t3_boole, axiom,
% 0.38/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.55  thf('17', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.55  thf(t37_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i]:
% 0.38/0.55         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.55  thf('20', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.38/0.55          | ((k1_xboole_0)
% 0.38/0.55              = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.38/0.55          | ((k1_xboole_0)
% 0.38/0.55              = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))))),
% 0.38/0.55      inference('demod', [status(thm)], ['16', '20', '21', '22'])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.38/0.55          | (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.55  thf(t6_zfmisc_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.38/0.55       ( ( A ) = ( B ) ) ))).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i]:
% 0.38/0.55         (((X17) = (X16))
% 0.38/0.55          | ~ (r1_tarski @ (k1_tarski @ X17) @ (k1_tarski @ X16)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.38/0.55          | ((X1) = (X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf(d7_xboole_0, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.38/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X0 : $i, X2 : $i]:
% 0.38/0.55         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.55          | ((X0) = (X1))
% 0.38/0.55          | (r1_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((r1_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.55  thf(t17_zfmisc_1, conjecture,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( A ) != ( B ) ) =>
% 0.38/0.55       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i,B:$i]:
% 0.38/0.55        ( ( ( A ) != ( B ) ) =>
% 0.38/0.55          ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t17_zfmisc_1])).
% 0.38/0.55  thf('30', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('31', plain, (((sk_B) = (sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('32', plain, (((sk_A) != (sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('33', plain, ($false),
% 0.38/0.55      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
