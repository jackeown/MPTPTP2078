%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dr4gTZ4Uhp

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:25 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   46 (  54 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  248 ( 331 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

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
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dr4gTZ4Uhp
% 0.14/0.37  % Computer   : n006.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 18:07:23 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 41 iterations in 0.020s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.23/0.50  thf(t2_tex_2, conjecture,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.23/0.50           ( r1_tarski @ A @ B ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]:
% 0.23/0.50        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.23/0.50          ( ![B:$i]:
% 0.23/0.50            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.23/0.50              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.23/0.50  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t17_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 0.23/0.50      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.23/0.50  thf(t1_tex_2, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.23/0.50           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X19 : $i, X20 : $i]:
% 0.23/0.50         ((v1_xboole_0 @ X19)
% 0.23/0.50          | ~ (v1_zfmisc_1 @ X19)
% 0.23/0.50          | ((X20) = (X19))
% 0.23/0.50          | ~ (r1_tarski @ X20 @ X19)
% 0.23/0.50          | (v1_xboole_0 @ X20))),
% 0.23/0.50      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 0.23/0.50          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.23/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.50          | (v1_xboole_0 @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf('4', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (((v1_xboole_0 @ sk_A)
% 0.23/0.50        | ~ (v1_zfmisc_1 @ sk_A)
% 0.23/0.50        | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.50  thf('6', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.23/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.23/0.50  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.23/0.50      inference('clc', [status(thm)], ['7', '8'])).
% 0.23/0.50  thf(t100_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X6 : $i, X7 : $i]:
% 0.23/0.50         ((k4_xboole_0 @ X6 @ X7)
% 0.23/0.50           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.23/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.23/0.50  thf(d10_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.50  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.50  thf(t11_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.50         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.23/0.50      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.50  thf(l32_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      (![X3 : $i, X5 : $i]:
% 0.23/0.50         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.23/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf(t21_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X13 : $i, X14 : $i]:
% 0.23/0.50         ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (X13))),
% 0.23/0.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      (![X6 : $i, X7 : $i]:
% 0.23/0.50         ((k4_xboole_0 @ X6 @ X7)
% 0.23/0.50           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.23/0.50           = (k5_xboole_0 @ X0 @ X0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['18', '19'])).
% 0.23/0.50  thf('21', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['17', '20'])).
% 0.23/0.50  thf('22', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['11', '21'])).
% 0.23/0.50  thf('23', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i]:
% 0.23/0.50         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.23/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.50  thf('24', plain,
% 0.23/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.50  thf('25', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.23/0.50  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
