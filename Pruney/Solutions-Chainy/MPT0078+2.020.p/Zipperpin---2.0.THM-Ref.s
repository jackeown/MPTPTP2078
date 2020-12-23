%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Eydz3EIz6C

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:55 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   60 (  81 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  334 ( 567 expanded)
%              Number of equality atoms :   33 (  57 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['6','15'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(demod,[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A = sk_C_1 ),
    inference('sup+',[status(thm)],['20','35'])).

thf('37',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Eydz3EIz6C
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.65/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.87  % Solved by: fo/fo7.sh
% 0.65/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.87  % done 747 iterations in 0.400s
% 0.65/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.87  % SZS output start Refutation
% 0.65/0.87  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.65/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.65/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.65/0.87  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.65/0.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.65/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.65/0.87  thf(sk_B_type, type, sk_B: $i > $i).
% 0.65/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.87  thf(t71_xboole_1, conjecture,
% 0.65/0.87    (![A:$i,B:$i,C:$i]:
% 0.65/0.87     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.65/0.87         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.65/0.87       ( ( A ) = ( C ) ) ))).
% 0.65/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.87    (~( ![A:$i,B:$i,C:$i]:
% 0.65/0.87        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.65/0.87            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.65/0.87          ( ( A ) = ( C ) ) ) )),
% 0.65/0.87    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.65/0.87  thf('0', plain,
% 0.65/0.87      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.65/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.87  thf(t7_xboole_1, axiom,
% 0.65/0.87    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.65/0.87  thf('1', plain,
% 0.65/0.87      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 0.65/0.87      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.65/0.87  thf('2', plain, ((r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1))),
% 0.65/0.87      inference('sup+', [status(thm)], ['0', '1'])).
% 0.65/0.87  thf(commutativity_k2_xboole_0, axiom,
% 0.65/0.87    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.65/0.87  thf('3', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.87  thf(t43_xboole_1, axiom,
% 0.65/0.87    (![A:$i,B:$i,C:$i]:
% 0.65/0.87     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.65/0.87       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.65/0.87  thf('4', plain,
% 0.65/0.87      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.87         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.65/0.87          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.65/0.87      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.65/0.87  thf('5', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.87         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.65/0.87          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 0.65/0.87      inference('sup-', [status(thm)], ['3', '4'])).
% 0.65/0.87  thf('6', plain, ((r1_tarski @ (k4_xboole_0 @ sk_C_1 @ sk_B_1) @ sk_A)),
% 0.65/0.87      inference('sup-', [status(thm)], ['2', '5'])).
% 0.65/0.87  thf('7', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.65/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.87  thf(t7_xboole_0, axiom,
% 0.65/0.87    (![A:$i]:
% 0.65/0.87     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.65/0.87          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.65/0.87  thf('8', plain,
% 0.65/0.87      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.65/0.87      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.65/0.87  thf(t4_xboole_0, axiom,
% 0.65/0.87    (![A:$i,B:$i]:
% 0.65/0.87     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.65/0.87            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.65/0.87       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.65/0.87            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.65/0.87  thf('9', plain,
% 0.65/0.87      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.65/0.87         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.65/0.87          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.65/0.87      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.65/0.87  thf('10', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]:
% 0.65/0.87         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.65/0.87      inference('sup-', [status(thm)], ['8', '9'])).
% 0.65/0.87  thf('11', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 0.65/0.87      inference('sup-', [status(thm)], ['7', '10'])).
% 0.65/0.87  thf(t47_xboole_1, axiom,
% 0.65/0.87    (![A:$i,B:$i]:
% 0.65/0.87     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.65/0.87  thf('12', plain,
% 0.65/0.87      (![X15 : $i, X16 : $i]:
% 0.65/0.87         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.65/0.87           = (k4_xboole_0 @ X15 @ X16))),
% 0.65/0.87      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.65/0.87  thf('13', plain,
% 0.65/0.87      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.65/0.87      inference('sup+', [status(thm)], ['11', '12'])).
% 0.65/0.87  thf(t3_boole, axiom,
% 0.65/0.87    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.65/0.87  thf('14', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.65/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.87  thf('15', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.65/0.87      inference('demod', [status(thm)], ['13', '14'])).
% 0.65/0.87  thf('16', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.65/0.87      inference('demod', [status(thm)], ['6', '15'])).
% 0.65/0.87  thf(t12_xboole_1, axiom,
% 0.65/0.87    (![A:$i,B:$i]:
% 0.65/0.87     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.65/0.87  thf('17', plain,
% 0.65/0.87      (![X7 : $i, X8 : $i]:
% 0.65/0.87         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.65/0.87      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.65/0.87  thf('18', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 0.65/0.87      inference('sup-', [status(thm)], ['16', '17'])).
% 0.65/0.87  thf('19', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.87  thf('20', plain, (((k2_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.65/0.87      inference('demod', [status(thm)], ['18', '19'])).
% 0.65/0.87  thf('21', plain,
% 0.65/0.87      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 0.65/0.87      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.65/0.87  thf('22', plain,
% 0.65/0.87      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.65/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.87  thf('23', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.87         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.65/0.87          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 0.65/0.87      inference('sup-', [status(thm)], ['3', '4'])).
% 0.65/0.87  thf('24', plain,
% 0.65/0.87      (![X0 : $i]:
% 0.65/0.87         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_A @ sk_B_1))
% 0.65/0.87          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B_1) @ sk_C_1))),
% 0.65/0.87      inference('sup-', [status(thm)], ['22', '23'])).
% 0.65/0.87  thf('25', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1)),
% 0.65/0.87      inference('sup-', [status(thm)], ['21', '24'])).
% 0.65/0.87  thf('26', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.65/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.87  thf('27', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]:
% 0.65/0.87         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.65/0.87      inference('sup-', [status(thm)], ['8', '9'])).
% 0.65/0.87  thf('28', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.65/0.87      inference('sup-', [status(thm)], ['26', '27'])).
% 0.65/0.87  thf('29', plain,
% 0.65/0.87      (![X15 : $i, X16 : $i]:
% 0.65/0.87         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.65/0.87           = (k4_xboole_0 @ X15 @ X16))),
% 0.65/0.87      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.65/0.87  thf('30', plain,
% 0.65/0.87      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.65/0.87      inference('sup+', [status(thm)], ['28', '29'])).
% 0.65/0.87  thf('31', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.65/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.87  thf('32', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.65/0.87      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.87  thf('33', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.65/0.87      inference('demod', [status(thm)], ['25', '32'])).
% 0.65/0.87  thf('34', plain,
% 0.65/0.87      (![X7 : $i, X8 : $i]:
% 0.65/0.87         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.65/0.87      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.65/0.87  thf('35', plain, (((k2_xboole_0 @ sk_A @ sk_C_1) = (sk_C_1))),
% 0.65/0.87      inference('sup-', [status(thm)], ['33', '34'])).
% 0.65/0.87  thf('36', plain, (((sk_A) = (sk_C_1))),
% 0.65/0.87      inference('sup+', [status(thm)], ['20', '35'])).
% 0.65/0.87  thf('37', plain, (((sk_A) != (sk_C_1))),
% 0.65/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.87  thf('38', plain, ($false),
% 0.65/0.87      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.65/0.87  
% 0.65/0.87  % SZS output end Refutation
% 0.65/0.87  
% 0.65/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
