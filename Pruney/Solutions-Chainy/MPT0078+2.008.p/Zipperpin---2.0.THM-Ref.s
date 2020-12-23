%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8rZykyWp2I

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:53 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   52 (  88 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  305 ( 616 expanded)
%              Number of equality atoms :   39 (  79 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X18 ) @ X17 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('22',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['20','21','28'])).

thf('30',plain,(
    sk_A = sk_C_1 ),
    inference('sup+',[status(thm)],['10','29'])).

thf('31',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8rZykyWp2I
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:50:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 577 iterations in 0.188s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(t71_xboole_1, conjecture,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.47/0.65         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.47/0.65       ( ( A ) = ( C ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.65        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.47/0.65            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.47/0.65          ( ( A ) = ( C ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.47/0.65  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t7_xboole_0, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.65          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.47/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.65  thf(t4_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.47/0.65          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.65  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['0', '3'])).
% 0.47/0.65  thf(t51_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.47/0.65       ( A ) ))).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.47/0.65           = (X23))),
% 0.47/0.65      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['4', '5'])).
% 0.47/0.65  thf(commutativity_k2_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.65  thf(t1_boole, axiom,
% 0.47/0.65    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.65  thf('8', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.47/0.65      inference('cnf', [status(esa)], [t1_boole])).
% 0.47/0.65  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['7', '8'])).
% 0.47/0.65  thf('10', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['6', '9'])).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('12', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.47/0.65      inference('cnf', [status(esa)], [t1_boole])).
% 0.47/0.65  thf(t46_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (![X19 : $i, X20 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.47/0.65  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['12', '13'])).
% 0.47/0.65  thf(t42_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.65       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X18) @ X17)
% 0.47/0.65           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 0.47/0.65              (k4_xboole_0 @ X18 @ X17)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.47/0.65           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['14', '15'])).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.65  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['7', '8'])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.47/0.65           = (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.47/0.65         = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.47/0.65      inference('sup+', [status(thm)], ['11', '19'])).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.47/0.65           = (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.47/0.65  thf('22', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.65  thf('24', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.47/0.65           = (X23))),
% 0.47/0.65      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1))
% 0.47/0.65         = (sk_C_1))),
% 0.47/0.65      inference('sup+', [status(thm)], ['24', '25'])).
% 0.47/0.65  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['7', '8'])).
% 0.47/0.65  thf('28', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.65  thf('29', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_C_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['20', '21', '28'])).
% 0.47/0.65  thf('30', plain, (((sk_A) = (sk_C_1))),
% 0.47/0.65      inference('sup+', [status(thm)], ['10', '29'])).
% 0.47/0.65  thf('31', plain, (((sk_A) != (sk_C_1))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('32', plain, ($false),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
