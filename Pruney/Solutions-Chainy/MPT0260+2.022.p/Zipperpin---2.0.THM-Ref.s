%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R8aPxw28SA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  258 ( 315 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t42_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X43: $i,X45: $i,X46: $i] :
      ( ( r1_tarski @ X45 @ ( k2_tarski @ X43 @ X46 ) )
      | ( X45
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('2',plain,(
    ! [X43: $i,X46: $i] :
      ( r1_tarski @ ( k1_tarski @ X43 ) @ ( k2_tarski @ X43 @ X46 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r2_hidden @ X40 @ X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ X41 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t54_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('14',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t54_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','16'])).

thf('18',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X40: $i,X42: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ X42 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['18','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R8aPxw28SA
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 72 iterations in 0.030s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(t55_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & 
% 0.20/0.48             ( r2_hidden @ A @ C ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t55_zfmisc_1])).
% 0.20/0.48  thf('0', plain, ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t42_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.20/0.48       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.20/0.48            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X43 : $i, X45 : $i, X46 : $i]:
% 0.20/0.48         ((r1_tarski @ X45 @ (k2_tarski @ X43 @ X46))
% 0.20/0.48          | ((X45) != (k1_tarski @ X43)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X43 : $i, X46 : $i]:
% 0.20/0.48         (r1_tarski @ (k1_tarski @ X43) @ (k2_tarski @ X43 @ X46))),
% 0.20/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.48  thf(t67_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.20/0.48         ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.48       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (((X9) = (k1_xboole_0))
% 0.20/0.48          | ~ (r1_tarski @ X9 @ X10)
% 0.20/0.48          | ~ (r1_tarski @ X9 @ X11)
% 0.20/0.48          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.48          | ~ (r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.20/0.48          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(t2_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.48  thf(d7_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.48       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.48  thf(t83_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.48  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf(l35_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48       ( r2_hidden @ A @ B ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X40 : $i, X41 : $i]:
% 0.20/0.48         ((r2_hidden @ X40 @ X41)
% 0.20/0.48          | ((k4_xboole_0 @ (k1_tarski @ X40) @ X41) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_tarski @ X0) != (k1_xboole_0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.48  thf(t54_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X47 : $i, X48 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k1_tarski @ X47) @ X48) | ~ (r2_hidden @ X47 @ X48))),
% 0.20/0.48      inference('cnf', [status(esa)], [t54_zfmisc_1])).
% 0.20/0.48  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['12', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.48          | ~ (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['4', '16'])).
% 0.20/0.48  thf('18', plain, (~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '17'])).
% 0.20/0.48  thf('19', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X40 : $i, X42 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ (k1_tarski @ X40) @ X42) = (k1_xboole_0))
% 0.20/0.48          | ~ (r2_hidden @ X40 @ X42))),
% 0.20/0.48      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_C) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf(t37_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 0.20/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.48  thf('25', plain, ($false), inference('demod', [status(thm)], ['18', '24'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
