%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LV0n1TgUac

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:53 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 107 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  365 ( 708 expanded)
%              Number of equality atoms :   43 (  85 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ~ ( v1_xboole_0 @ X29 )
      | ( X28 = X29 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X23 ) @ X22 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('29',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('31',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('38',plain,(
    sk_A = sk_C_1 ),
    inference(demod,[status(thm)],['10','36','37'])).

thf('39',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LV0n1TgUac
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 198 iterations in 0.089s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.53  thf(t71_xboole_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.19/0.53         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.19/0.53       ( ( A ) = ( C ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.53        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.19/0.53            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.19/0.53          ( ( A ) = ( C ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.19/0.53  thf('0', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d1_xboole_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.53  thf(t4_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.19/0.53          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.53  thf('4', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.53  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.53  thf(t8_boole, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ X28) | ~ (v1_xboole_0 @ X29) | ((X28) = (X29)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t8_boole])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf('8', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '7'])).
% 0.19/0.53  thf(t51_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.19/0.53       ( A ) ))).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X26 : $i, X27 : $i]:
% 0.19/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))
% 0.19/0.53           = (X26))),
% 0.19/0.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1))
% 0.19/0.53         = (sk_C_1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t3_boole, axiom,
% 0.19/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.53  thf('12', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.53  thf(t48_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X24 : $i, X25 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.19/0.53           = (k3_xboole_0 @ X24 @ X25))),
% 0.19/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['12', '13'])).
% 0.19/0.53  thf(t2_boole, axiom,
% 0.19/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.53  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.53  thf(t42_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.53       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X23) @ X22)
% 0.19/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 0.19/0.53              (k4_xboole_0 @ X23 @ X22)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.19/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.53  thf(t1_boole, axiom,
% 0.19/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.53  thf('21', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.53  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.19/0.53           = (k4_xboole_0 @ X1 @ X0))),
% 0.19/0.53      inference('demod', [status(thm)], ['18', '19', '22'])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.19/0.53         = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['11', '23'])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.19/0.53           = (k4_xboole_0 @ X1 @ X0))),
% 0.19/0.53      inference('demod', [status(thm)], ['18', '19', '22'])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.53  thf('27', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.53  thf('29', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf('31', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (![X26 : $i, X27 : $i]:
% 0.19/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))
% 0.19/0.53           = (X26))),
% 0.19/0.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.53  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.19/0.53  thf('35', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.53  thf('36', plain, (((sk_A) = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['26', '35'])).
% 0.19/0.53  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.19/0.53  thf('38', plain, (((sk_A) = (sk_C_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['10', '36', '37'])).
% 0.19/0.53  thf('39', plain, (((sk_A) != (sk_C_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('40', plain, ($false),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
