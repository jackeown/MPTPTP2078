%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AWtKEJ3fpC

% Computer   : n025.cluster.edu
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
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ ( sk_D @ X8 @ X7 @ X6 ) @ X8 )
      | ( X6
        = ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ ( sk_D @ X8 @ X7 @ X6 ) @ X7 )
      | ( X6
        = ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ~ ( r1_tarski @ ( sk_D @ X8 @ X7 @ X6 ) @ X6 )
      | ( X6
        = ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
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

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AWtKEJ3fpC
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 165 iterations in 0.095s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(l3_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.38/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (![X14 : $i, X15 : $i]:
% 0.38/0.56         ((r1_tarski @ X14 @ (k1_tarski @ X15)) | ((X14) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.38/0.56  thf('1', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.56  thf('2', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.56  thf(t20_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.38/0.56         ( ![D:$i]:
% 0.38/0.56           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.38/0.56             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.38/0.56       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X6 @ X7)
% 0.38/0.56          | ~ (r1_tarski @ X6 @ X8)
% 0.38/0.56          | (r1_tarski @ (sk_D @ X8 @ X7 @ X6) @ X8)
% 0.38/0.56          | ((X6) = (k3_xboole_0 @ X7 @ X8)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.38/0.56          | (r1_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ k1_xboole_0) @ X1)
% 0.38/0.56          | ~ (r1_tarski @ k1_xboole_0 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_tarski @ 
% 0.38/0.56           (sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0) @ 
% 0.38/0.56           (k1_tarski @ X0))
% 0.38/0.56          | ((k1_xboole_0)
% 0.38/0.56              = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i]:
% 0.38/0.56         (((X14) = (k1_tarski @ X13))
% 0.38/0.56          | ((X14) = (k1_xboole_0))
% 0.38/0.56          | ~ (r1_tarski @ X14 @ (k1_tarski @ X13)))),
% 0.38/0.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.38/0.56          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0)
% 0.38/0.56              = (k1_xboole_0))
% 0.38/0.56          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0)
% 0.38/0.56              = (k1_tarski @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('8', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.56  thf('9', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X6 @ X7)
% 0.38/0.56          | ~ (r1_tarski @ X6 @ X8)
% 0.38/0.56          | (r1_tarski @ (sk_D @ X8 @ X7 @ X6) @ X7)
% 0.38/0.56          | ((X6) = (k3_xboole_0 @ X7 @ X8)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.38/0.56          | (r1_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ k1_xboole_0) @ 
% 0.38/0.56             (k1_tarski @ X0))
% 0.38/0.56          | ~ (r1_tarski @ k1_xboole_0 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_tarski @ 
% 0.38/0.56           (sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0) @ 
% 0.38/0.56           (k1_tarski @ X1))
% 0.38/0.56          | ((k1_xboole_0)
% 0.38/0.56              = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '11'])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.38/0.56          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0)
% 0.38/0.56              = (k1_xboole_0))
% 0.38/0.56          | ((k1_xboole_0)
% 0.38/0.56              = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.38/0.56          | ((k1_xboole_0)
% 0.38/0.56              = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 0.38/0.56      inference('sup+', [status(thm)], ['7', '12'])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.38/0.56          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ k1_xboole_0)
% 0.38/0.56              = (k1_xboole_0))
% 0.38/0.56          | (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X6 @ X7)
% 0.38/0.56          | ~ (r1_tarski @ X6 @ X8)
% 0.38/0.56          | ~ (r1_tarski @ (sk_D @ X8 @ X7 @ X6) @ X6)
% 0.38/0.56          | ((X6) = (k3_xboole_0 @ X7 @ X8)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.38/0.56          | (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.38/0.56          | ((k1_xboole_0)
% 0.38/0.56              = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.38/0.56          | ((k1_xboole_0)
% 0.38/0.56              = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.38/0.56          | ~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X1))
% 0.38/0.56          | ~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf(t3_boole, axiom,
% 0.38/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.56  thf('17', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.56  thf(l32_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X3 : $i, X4 : $i]:
% 0.38/0.56         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('20', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X15))),
% 0.38/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.38/0.56          | ((k1_xboole_0)
% 0.38/0.56              = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.38/0.56          | ((k1_xboole_0)
% 0.38/0.56              = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))))),
% 0.38/0.56      inference('demod', [status(thm)], ['16', '20', '21', '22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.38/0.56          | (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.56  thf(t6_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.38/0.56       ( ( A ) = ( B ) ) ))).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X16 : $i, X17 : $i]:
% 0.38/0.56         (((X17) = (X16))
% 0.38/0.56          | ~ (r1_tarski @ (k1_tarski @ X17) @ (k1_tarski @ X16)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.38/0.56          | ((X1) = (X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.56  thf(d7_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.38/0.56       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X0 : $i, X2 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.56          | ((X0) = (X1))
% 0.38/0.56          | (r1_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.56  thf(t17_zfmisc_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( A ) != ( B ) ) =>
% 0.38/0.56       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( ( A ) != ( B ) ) =>
% 0.38/0.56          ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t17_zfmisc_1])).
% 0.38/0.56  thf('30', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('31', plain, (((sk_B) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.56  thf('32', plain, (((sk_A) != (sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('33', plain, ($false),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
