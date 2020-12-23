%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IeuS5q8zA6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:15 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   60 (  78 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  397 ( 619 expanded)
%              Number of equality atoms :   41 (  66 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
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

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_C ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('35',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ X33 )
        = X33 )
      | ~ ( r2_hidden @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('36',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['22','33','36'])).

thf('38',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IeuS5q8zA6
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.69  % Solved by: fo/fo7.sh
% 0.52/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.69  % done 619 iterations in 0.241s
% 0.52/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.69  % SZS output start Refutation
% 0.52/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.69  thf(t148_zfmisc_1, conjecture,
% 0.52/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.69     ( ( ( r1_tarski @ A @ B ) & 
% 0.52/0.69         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.52/0.69         ( r2_hidden @ D @ A ) ) =>
% 0.52/0.69       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.52/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.69        ( ( ( r1_tarski @ A @ B ) & 
% 0.52/0.69            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.52/0.69            ( r2_hidden @ D @ A ) ) =>
% 0.52/0.69          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.52/0.69    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.52/0.69  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.69  thf('1', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.69  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf(t28_xboole_1, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.69  thf('3', plain,
% 0.52/0.69      (![X15 : $i, X16 : $i]:
% 0.52/0.69         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.52/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.69  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.69  thf('5', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.69  thf('6', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.52/0.69      inference('demod', [status(thm)], ['4', '5'])).
% 0.52/0.69  thf(t16_xboole_1, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.69       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.52/0.69  thf('7', plain,
% 0.52/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.69         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.52/0.69           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.52/0.69      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.52/0.69  thf(t17_xboole_1, axiom,
% 0.52/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.69  thf('8', plain,
% 0.52/0.69      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.52/0.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.52/0.69  thf('9', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.69         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.52/0.69          (k3_xboole_0 @ X2 @ X1))),
% 0.52/0.69      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.69  thf('10', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.52/0.69      inference('sup+', [status(thm)], ['6', '9'])).
% 0.52/0.69  thf('11', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.52/0.69      inference('sup+', [status(thm)], ['1', '10'])).
% 0.52/0.69  thf('12', plain,
% 0.52/0.69      ((r1_tarski @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D))),
% 0.52/0.69      inference('sup+', [status(thm)], ['0', '11'])).
% 0.52/0.69  thf('13', plain,
% 0.52/0.69      (![X15 : $i, X16 : $i]:
% 0.52/0.69         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.52/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.69  thf('14', plain,
% 0.52/0.69      (((k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D))
% 0.52/0.69         = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.69  thf('15', plain,
% 0.52/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.69         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.52/0.69           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.52/0.69      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.52/0.69  thf('16', plain,
% 0.52/0.69      (((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))
% 0.52/0.69         = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.52/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.52/0.69  thf('17', plain,
% 0.52/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.69         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.52/0.69           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.52/0.69      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.52/0.69  thf('18', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.69  thf(t22_xboole_1, axiom,
% 0.52/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.52/0.69  thf('19', plain,
% 0.52/0.69      (![X10 : $i, X11 : $i]:
% 0.52/0.69         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.52/0.69      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.52/0.69  thf('20', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.52/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.52/0.69  thf('21', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.69         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.52/0.69           = (X0))),
% 0.52/0.69      inference('sup+', [status(thm)], ['17', '20'])).
% 0.52/0.69  thf('22', plain,
% 0.52/0.69      (((k2_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_C @ sk_A))
% 0.52/0.69         = (k1_tarski @ sk_D))),
% 0.52/0.69      inference('sup+', [status(thm)], ['16', '21'])).
% 0.52/0.69  thf('23', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('24', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.69  thf('25', plain,
% 0.52/0.69      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.52/0.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.52/0.69  thf('26', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.52/0.69      inference('sup+', [status(thm)], ['24', '25'])).
% 0.52/0.69  thf('27', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_C)),
% 0.52/0.69      inference('sup+', [status(thm)], ['23', '26'])).
% 0.52/0.69  thf('28', plain,
% 0.52/0.69      (![X15 : $i, X16 : $i]:
% 0.52/0.69         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.52/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.69  thf('29', plain,
% 0.52/0.69      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_C) = (k1_tarski @ sk_D))),
% 0.52/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.69  thf('30', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.69  thf('31', plain,
% 0.52/0.69      (((k3_xboole_0 @ sk_C @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.52/0.69      inference('demod', [status(thm)], ['29', '30'])).
% 0.52/0.69  thf(t23_xboole_1, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.52/0.69       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.52/0.69  thf('32', plain,
% 0.52/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.69         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14))
% 0.52/0.69           = (k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ 
% 0.52/0.69              (k3_xboole_0 @ X12 @ X14)))),
% 0.52/0.69      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.52/0.69  thf('33', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         ((k3_xboole_0 @ sk_C @ (k2_xboole_0 @ (k1_tarski @ sk_D) @ X0))
% 0.52/0.69           = (k2_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.52/0.69      inference('sup+', [status(thm)], ['31', '32'])).
% 0.52/0.69  thf('34', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf(l22_zfmisc_1, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ( r2_hidden @ A @ B ) =>
% 0.52/0.69       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.52/0.69  thf('35', plain,
% 0.52/0.69      (![X33 : $i, X34 : $i]:
% 0.52/0.69         (((k2_xboole_0 @ (k1_tarski @ X34) @ X33) = (X33))
% 0.52/0.69          | ~ (r2_hidden @ X34 @ X33))),
% 0.52/0.69      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.52/0.69  thf('36', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.52/0.69  thf('37', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D))),
% 0.52/0.69      inference('demod', [status(thm)], ['22', '33', '36'])).
% 0.52/0.69  thf('38', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('39', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.69  thf('40', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.52/0.69      inference('demod', [status(thm)], ['38', '39'])).
% 0.52/0.69  thf('41', plain, ($false),
% 0.52/0.69      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.52/0.69  
% 0.52/0.69  % SZS output end Refutation
% 0.52/0.69  
% 0.52/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
