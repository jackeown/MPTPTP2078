%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zn72annuGU

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  208 ( 283 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_zfmisc_1 @ X15 )
      | ( X16 = X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','16'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zn72annuGU
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 41 iterations in 0.010s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(t2_tex_2, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.22/0.47           ( r1_tarski @ A @ B ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.22/0.47          ( ![B:$i]:
% 0.22/0.47            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.22/0.47              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.22/0.47  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t17_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.22/0.47      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.47  thf(t1_tex_2, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.47           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X15 : $i, X16 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ X15)
% 0.22/0.47          | ~ (v1_zfmisc_1 @ X15)
% 0.22/0.47          | ((X16) = (X15))
% 0.22/0.47          | ~ (r1_tarski @ X16 @ X15)
% 0.22/0.47          | (v1_xboole_0 @ X16))),
% 0.22/0.47      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 0.22/0.47          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.22/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.47          | (v1_xboole_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf('4', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (((v1_xboole_0 @ sk_A)
% 0.22/0.47        | ~ (v1_zfmisc_1 @ sk_A)
% 0.22/0.47        | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.47  thf('6', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.47  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.47      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf(t100_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         ((k4_xboole_0 @ X3 @ X4)
% 0.22/0.47           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.22/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.47  thf(t21_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (![X7 : $i, X8 : $i]:
% 0.22/0.47         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         ((k4_xboole_0 @ X3 @ X4)
% 0.22/0.47           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.22/0.47           = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf(t46_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X9 : $i, X10 : $i]:
% 0.22/0.47         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.47  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.47      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['11', '16'])).
% 0.22/0.47  thf(l32_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.22/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.47  thf('20', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.47  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.34/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
