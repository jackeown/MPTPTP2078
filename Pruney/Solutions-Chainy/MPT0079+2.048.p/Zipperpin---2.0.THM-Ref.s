%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DBtLEzvC2U

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:03 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   64 (  83 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  389 ( 577 expanded)
%              Number of equality atoms :   31 (  52 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X6 @ ( k2_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 )
      | ( ( k4_xboole_0 @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('16',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','25'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( ( k4_xboole_0 @ X10 @ X9 )
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','30'])).

thf('32',plain,(
    ~ ( r1_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['32','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DBtLEzvC2U
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 307 iterations in 0.083s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.54  thf(t3_boole, axiom,
% 0.37/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.54  thf('0', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.54  thf(t36_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.37/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.54  thf('2', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.54      inference('sup+', [status(thm)], ['0', '1'])).
% 0.37/0.54  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.54      inference('sup+', [status(thm)], ['0', '1'])).
% 0.37/0.54  thf(t10_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.54         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ X6 @ (k2_xboole_0 @ X8 @ X7)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.54  thf(t72_xboole_1, conjecture,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.37/0.54         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.37/0.54       ( ( C ) = ( B ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.37/0.54            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.37/0.54          ( ( C ) = ( B ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t43_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.37/0.54       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.54         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.37/0.54          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.37/0.54          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 0.37/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.54  thf('9', plain, ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_D)),
% 0.37/0.54      inference('sup-', [status(thm)], ['5', '8'])).
% 0.37/0.54  thf(t67_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.37/0.54         ( r1_xboole_0 @ B @ C ) ) =>
% 0.37/0.54       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.54         (((X25) = (k1_xboole_0))
% 0.37/0.54          | ~ (r1_tarski @ X25 @ X26)
% 0.37/0.54          | ~ (r1_tarski @ X25 @ X27)
% 0.37/0.54          | ~ (r1_xboole_0 @ X26 @ X27))),
% 0.37/0.54      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.37/0.54          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)
% 0.37/0.54          | ((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t7_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 0.37/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.54  thf('14', plain, ((r1_tarski @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.54      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.54         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.37/0.54          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.37/0.54  thf('16', plain, ((r1_tarski @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B)),
% 0.37/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.54  thf(l32_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X3 : $i, X5 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (((k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.54  thf('19', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(d7_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.54  thf('21', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.54  thf(t47_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      (![X17 : $i, X18 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.37/0.54           = (k4_xboole_0 @ X17 @ X18))),
% 0.37/0.54      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.37/0.54      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.54  thf('24', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.54  thf('25', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.54  thf('26', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['18', '25'])).
% 0.37/0.54  thf(t32_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.37/0.54       ( ( A ) = ( B ) ) ))).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (![X9 : $i, X10 : $i]:
% 0.37/0.54         (((X10) = (X9))
% 0.37/0.54          | ((k4_xboole_0 @ X10 @ X9) != (k4_xboole_0 @ X9 @ X10)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      ((((k4_xboole_0 @ sk_B @ sk_C) != (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.54  thf('29', plain, (((sk_C) != (sk_B))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('30', plain, (((k4_xboole_0 @ sk_B @ sk_C) != (k1_xboole_0))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.37/0.54          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['11', '30'])).
% 0.37/0.54  thf('32', plain, (~ (r1_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.54      inference('sup-', [status(thm)], ['2', '31'])).
% 0.37/0.54  thf('33', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.37/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.54  thf('35', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.54      inference('sup+', [status(thm)], ['0', '1'])).
% 0.37/0.54  thf(t64_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.37/0.54         ( r1_xboole_0 @ B @ D ) ) =>
% 0.37/0.54       ( r1_xboole_0 @ A @ C ) ))).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X21 @ X22)
% 0.37/0.54          | ~ (r1_tarski @ X21 @ X23)
% 0.37/0.54          | ~ (r1_tarski @ X22 @ X24)
% 0.37/0.54          | ~ (r1_xboole_0 @ X23 @ X24))),
% 0.37/0.54      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.37/0.54  thf('37', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         (~ (r1_xboole_0 @ X0 @ X1)
% 0.37/0.54          | ~ (r1_tarski @ X2 @ X1)
% 0.37/0.54          | (r1_xboole_0 @ X0 @ X2))),
% 0.37/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.54  thf('38', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.54          | ~ (r1_xboole_0 @ X2 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['34', '37'])).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      (![X0 : $i]: (r1_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['33', '38'])).
% 0.37/0.54  thf('40', plain, ($false), inference('demod', [status(thm)], ['32', '39'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
