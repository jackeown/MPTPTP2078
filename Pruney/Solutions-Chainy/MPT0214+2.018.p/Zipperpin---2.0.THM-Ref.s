%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IuKtFblKam

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:46 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  238 ( 289 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X34 != X33 )
      | ( r2_hidden @ X34 @ X35 )
      | ( X35
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X33: $i] :
      ( r2_hidden @ X33 @ ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X71: $i,X72: $i] :
      ( ( X72
        = ( k1_tarski @ X71 ) )
      | ( X72 = k1_xboole_0 )
      | ~ ( r1_tarski @ X72 @ ( k1_tarski @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('4',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X35 )
      | ( X36 = X33 )
      | ( X35
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X33: $i,X36: $i] :
      ( ( X36 = X33 )
      | ~ ( r2_hidden @ X36 @ ( k1_tarski @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( sk_A = sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X33: $i] :
      ( r2_hidden @ X33 @ ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ X18 )
      | ( ( k4_xboole_0 @ X16 @ X18 )
       != X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['14','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IuKtFblKam
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 190 iterations in 0.081s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(d1_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.54         (((X34) != (X33))
% 0.35/0.54          | (r2_hidden @ X34 @ X35)
% 0.35/0.54          | ((X35) != (k1_tarski @ X33)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.54  thf('1', plain, (![X33 : $i]: (r2_hidden @ X33 @ (k1_tarski @ X33))),
% 0.35/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.35/0.54  thf(t6_zfmisc_1, conjecture,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.35/0.54       ( ( A ) = ( B ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i]:
% 0.35/0.54        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.35/0.54          ( ( A ) = ( B ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.35/0.54  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(l3_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.35/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X71 : $i, X72 : $i]:
% 0.35/0.54         (((X72) = (k1_tarski @ X71))
% 0.35/0.54          | ((X72) = (k1_xboole_0))
% 0.35/0.54          | ~ (r1_tarski @ X72 @ (k1_tarski @ X71)))),
% 0.35/0.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.35/0.54        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B_1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X33 : $i, X35 : $i, X36 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X36 @ X35)
% 0.35/0.54          | ((X36) = (X33))
% 0.35/0.54          | ((X35) != (k1_tarski @ X33)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X33 : $i, X36 : $i]:
% 0.35/0.54         (((X36) = (X33)) | ~ (r2_hidden @ X36 @ (k1_tarski @ X33)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.35/0.54          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.35/0.54          | ((X0) = (sk_B_1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((((sk_A) = (sk_B_1)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '7'])).
% 0.35/0.54  thf('9', plain, (((sk_A) != (sk_B_1))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('10', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('11', plain, (![X33 : $i]: (r2_hidden @ X33 @ (k1_tarski @ X33))),
% 0.35/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.35/0.54  thf(d1_xboole_0, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.35/0.54  thf('13', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.54  thf('14', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.54      inference('sup-', [status(thm)], ['10', '13'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.35/0.54  thf(t46_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (![X13 : $i, X14 : $i]:
% 0.35/0.54         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.35/0.54  thf(t83_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X16 : $i, X18 : $i]:
% 0.35/0.54         ((r1_xboole_0 @ X16 @ X18) | ((k4_xboole_0 @ X16 @ X18) != (X16)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((k1_xboole_0) != (X0))
% 0.35/0.54          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (![X1 : $i]:
% 0.35/0.54         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.35/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.54  thf(t21_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X9 : $i, X10 : $i]:
% 0.35/0.54         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.35/0.54      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.35/0.54  thf(t4_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.35/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.35/0.54          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.35/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X2 @ X0)
% 0.35/0.54          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.54  thf('23', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.35/0.54      inference('sup-', [status(thm)], ['19', '22'])).
% 0.35/0.54  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.54      inference('sup-', [status(thm)], ['15', '23'])).
% 0.35/0.54  thf('25', plain, ($false), inference('demod', [status(thm)], ['14', '24'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
