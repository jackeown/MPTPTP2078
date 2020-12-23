%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vLEYPu4lJh

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 ( 340 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t55_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          & ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t55_zfmisc_1])).

thf('0',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X41: $i,X43: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ X43 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference(simplify,[status(thm)],['5'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ ( k2_tarski @ X44 @ X47 ) )
      | ( X46
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('8',plain,(
    ! [X44: $i,X47: $i] :
      ( r1_tarski @ ( k1_tarski @ X44 ) @ ( k2_tarski @ X44 @ X47 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('16',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
       != ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('19',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ X42 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference(clc,[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['6','23'])).

thf('25',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vLEYPu4lJh
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 259 iterations in 0.095s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(t55_zfmisc_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & 
% 0.21/0.55             ( r2_hidden @ A @ C ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t55_zfmisc_1])).
% 0.21/0.55  thf('0', plain, ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(l35_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.55       ( r2_hidden @ A @ B ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X41 : $i, X43 : $i]:
% 0.21/0.55         (((k4_xboole_0 @ (k1_tarski @ X41) @ X43) = (k1_xboole_0))
% 0.21/0.55          | ~ (r2_hidden @ X41 @ X43))),
% 0.21/0.55      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_C) = (k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf(l32_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55        | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.55  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 0.21/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.55  thf(l45_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.21/0.55       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.55            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X44 : $i, X46 : $i, X47 : $i]:
% 0.21/0.55         ((r1_tarski @ X46 @ (k2_tarski @ X44 @ X47))
% 0.21/0.55          | ((X46) != (k1_tarski @ X44)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X44 : $i, X47 : $i]:
% 0.21/0.55         (r1_tarski @ (k1_tarski @ X44) @ (k2_tarski @ X44 @ X47))),
% 0.21/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.55  thf(t67_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.55         ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.55       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         (((X7) = (k1_xboole_0))
% 0.21/0.55          | ~ (r1_tarski @ X7 @ X8)
% 0.21/0.55          | ~ (r1_tarski @ X7 @ X9)
% 0.21/0.55          | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.55          | ~ (r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.21/0.55          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf(t3_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.55  thf('11', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf(t48_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.21/0.55           = (k3_xboole_0 @ X5 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf(t2_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.55  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf(l33_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.55       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X38 : $i, X39 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X38 @ X39)
% 0.21/0.55          | ((k4_xboole_0 @ (k1_tarski @ X38) @ X39) != (k1_tarski @ X38)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X41 : $i, X42 : $i]:
% 0.21/0.55         ((r2_hidden @ X41 @ X42)
% 0.21/0.55          | ((k4_xboole_0 @ (k1_tarski @ X41) @ X42) != (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.55  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['17', '21'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.21/0.55          | ~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.21/0.55      inference('clc', [status(thm)], ['10', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i]: ~ (r1_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '23'])).
% 0.21/0.55  thf('25', plain, ($false), inference('sup-', [status(thm)], ['0', '24'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
