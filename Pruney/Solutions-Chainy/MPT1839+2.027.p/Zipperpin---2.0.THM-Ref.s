%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o5S2G9m6Dv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  51 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  238 ( 304 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_zfmisc_1 @ X19 )
      | ( X20 = X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( v1_xboole_0 @ X20 ) ) ),
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

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('17',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o5S2G9m6Dv
% 0.12/0.35  % Computer   : n023.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 13:27:36 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 79 iterations in 0.052s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(t2_tex_2, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.22/0.55           ( r1_tarski @ A @ B ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.22/0.55              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.22/0.55  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t17_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.22/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.55  thf(t1_tex_2, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.55           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X19 : $i, X20 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X19)
% 0.22/0.55          | ~ (v1_zfmisc_1 @ X19)
% 0.22/0.55          | ((X20) = (X19))
% 0.22/0.55          | ~ (r1_tarski @ X20 @ X19)
% 0.22/0.55          | (v1_xboole_0 @ X20))),
% 0.22/0.55      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 0.22/0.55          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.22/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.55          | (v1_xboole_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.55  thf('4', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | ~ (v1_zfmisc_1 @ sk_A)
% 0.22/0.55        | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.55  thf('6', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.55  thf(t96_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X17 : $i, X18 : $i]:
% 0.22/0.55         (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ (k5_xboole_0 @ X17 @ X18))),
% 0.22/0.55      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.22/0.55  thf(t107_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.22/0.55       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.55         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.55         ((r1_xboole_0 @ X3 @ (k3_xboole_0 @ X4 @ X5))
% 0.22/0.55          | ~ (r1_tarski @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf(t69_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.55       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X14 : $i, X15 : $i]:
% 0.22/0.55         (~ (r1_xboole_0 @ X14 @ X15)
% 0.22/0.55          | ~ (r1_tarski @ X14 @ X15)
% 0.22/0.55          | (v1_xboole_0 @ X14))),
% 0.22/0.55      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.22/0.55          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.55        | (v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['9', '14'])).
% 0.22/0.55  thf(t36_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.22/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.55  thf('17', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf(t6_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X16 : $i]: (((X16) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X16))),
% 0.22/0.55      inference('cnf', [status(esa)], [t6_boole])).
% 0.22/0.55  thf('19', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf(t37_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X11 : $i, X12 : $i]:
% 0.22/0.55         ((r1_tarski @ X11 @ X12)
% 0.22/0.55          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.55  thf('22', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.55      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.55  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
