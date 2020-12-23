%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8MyCIUx79o

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:33 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 100 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  455 ( 718 expanded)
%              Number of equality atoms :   45 (  80 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X35 != X34 )
      | ( r2_hidden @ X35 @ X36 )
      | ( X36
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X34: $i] :
      ( r2_hidden @ X34 @ ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k5_xboole_0 @ X6 @ X8 ) )
      | ( r2_hidden @ X5 @ X8 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X50 ) @ X49 )
        = X49 )
      | ~ ( r2_hidden @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('11',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('27',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X37 @ X36 )
      | ( X37 = X34 )
      | ( X36
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X34: $i,X37: $i] :
      ( ( X37 = X34 )
      | ~ ( r2_hidden @ X37 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X34: $i] :
      ( r2_hidden @ X34 @ ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('34',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('41',plain,(
    ! [X2: $i] :
      ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference('sup-',[status(thm)],['34','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8MyCIUx79o
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 217 iterations in 0.124s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(t18_zfmisc_1, conjecture,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.57         ( k1_tarski @ A ) ) =>
% 0.37/0.57       ( ( A ) = ( B ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i]:
% 0.37/0.57        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.57            ( k1_tarski @ A ) ) =>
% 0.37/0.57          ( ( A ) = ( B ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.37/0.57         = (k1_tarski @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.37/0.57         = (k1_tarski @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.57  thf(t100_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X13 @ X14)
% 0.37/0.57           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.37/0.57         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf(d1_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.57         (((X35) != (X34))
% 0.37/0.57          | (r2_hidden @ X35 @ X36)
% 0.37/0.57          | ((X36) != (k1_tarski @ X34)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.57  thf('6', plain, (![X34 : $i]: (r2_hidden @ X34 @ (k1_tarski @ X34))),
% 0.37/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.57  thf(t1_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.37/0.57       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.37/0.57         ((r2_hidden @ X5 @ (k5_xboole_0 @ X6 @ X8))
% 0.37/0.57          | (r2_hidden @ X5 @ X8)
% 0.37/0.57          | ~ (r2_hidden @ X5 @ X6))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r2_hidden @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (((r2_hidden @ sk_B @ 
% 0.37/0.57         (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.37/0.57        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['4', '8'])).
% 0.37/0.57  thf(l22_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r2_hidden @ A @ B ) =>
% 0.37/0.57       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X49 : $i, X50 : $i]:
% 0.37/0.57         (((k2_xboole_0 @ (k1_tarski @ X50) @ X49) = (X49))
% 0.37/0.57          | ~ (r2_hidden @ X50 @ X49))),
% 0.37/0.57      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.37/0.57        | ((k2_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.37/0.57            (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.37/0.57            = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf(t79_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.37/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.57  thf(d7_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X2 : $i, X3 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf(t23_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.37/0.57       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.37/0.57           = (k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 0.37/0.57              (k3_xboole_0 @ X17 @ X19)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.37/0.57           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf(t22_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X15 : $i, X16 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)) = (X15))),
% 0.37/0.57      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.37/0.57  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.37/0.57           = (k3_xboole_0 @ X0 @ X2))),
% 0.37/0.57      inference('demod', [status(thm)], ['18', '21'])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.37/0.57          (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.37/0.57          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.37/0.57        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['11', '22'])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.37/0.57         = (k1_tarski @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.37/0.57        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X37 @ X36)
% 0.37/0.57          | ((X37) = (X34))
% 0.37/0.57          | ((X36) != (k1_tarski @ X34)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X34 : $i, X37 : $i]:
% 0.37/0.57         (((X37) = (X34)) | ~ (r2_hidden @ X37 @ (k1_tarski @ X34)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_B) = (sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['27', '29'])).
% 0.37/0.57  thf('31', plain, (((sk_A) != (sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('32', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.37/0.57  thf('33', plain, (![X34 : $i]: (r2_hidden @ X34 @ (k1_tarski @ X34))),
% 0.37/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.57  thf('34', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.37/0.57      inference('sup+', [status(thm)], ['32', '33'])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf(t4_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.37/0.57          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.57          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X2 @ k1_xboole_0)
% 0.37/0.57          | ~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['35', '38'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.37/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.57  thf('41', plain, (![X2 : $i]: ~ (r2_hidden @ X2 @ k1_xboole_0)),
% 0.37/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.57  thf('42', plain, ($false), inference('sup-', [status(thm)], ['34', '41'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
