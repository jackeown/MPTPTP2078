%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Feoj43jSe

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:21 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   62 (  80 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  376 ( 580 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27
        = ( k1_tarski @ X26 ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('7',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('9',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ sk_B )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(simplify,[status(thm)],['28'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( ( k3_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['34'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('37',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['2','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Feoj43jSe
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.01/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.01/1.20  % Solved by: fo/fo7.sh
% 1.01/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.20  % done 1370 iterations in 0.746s
% 1.01/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.01/1.20  % SZS output start Refutation
% 1.01/1.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.01/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.01/1.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.01/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.20  thf(sk_C_type, type, sk_C: $i).
% 1.01/1.20  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.01/1.20  thf(sk_D_type, type, sk_D: $i).
% 1.01/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.01/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.20  thf(t149_zfmisc_1, conjecture,
% 1.01/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.20     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.01/1.20         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.01/1.20       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.01/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.20    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.20        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.01/1.20            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.01/1.20          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.01/1.20    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.01/1.20  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(commutativity_k2_xboole_0, axiom,
% 1.01/1.20    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.01/1.20  thf('1', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.01/1.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.01/1.20  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_B)),
% 1.01/1.20      inference('demod', [status(thm)], ['0', '1'])).
% 1.01/1.20  thf('3', plain,
% 1.01/1.20      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(commutativity_k3_xboole_0, axiom,
% 1.01/1.20    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.01/1.20  thf('4', plain,
% 1.01/1.20      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.01/1.20      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.20  thf('5', plain,
% 1.01/1.20      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['3', '4'])).
% 1.01/1.20  thf(l3_zfmisc_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.01/1.20       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.01/1.20  thf('6', plain,
% 1.01/1.20      (![X26 : $i, X27 : $i]:
% 1.01/1.20         (((X27) = (k1_tarski @ X26))
% 1.01/1.20          | ((X27) = (k1_xboole_0))
% 1.01/1.20          | ~ (r1_tarski @ X27 @ (k1_tarski @ X26)))),
% 1.01/1.20      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.01/1.20  thf('7', plain,
% 1.01/1.20      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.01/1.20        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['5', '6'])).
% 1.01/1.20  thf(t17_xboole_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.01/1.20  thf('8', plain,
% 1.01/1.20      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 1.01/1.20      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.01/1.20  thf('9', plain,
% 1.01/1.20      (((r1_tarski @ (k1_tarski @ sk_D) @ sk_B)
% 1.01/1.20        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.01/1.20      inference('sup+', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('10', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(d7_xboole_0, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.01/1.20       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.01/1.20  thf('11', plain,
% 1.01/1.20      (![X4 : $i, X5 : $i]:
% 1.01/1.20         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.01/1.20      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.01/1.20  thf('12', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['10', '11'])).
% 1.01/1.20  thf('13', plain,
% 1.01/1.20      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.01/1.20      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.20  thf('14', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 1.01/1.20      inference('demod', [status(thm)], ['12', '13'])).
% 1.01/1.20  thf('15', plain,
% 1.01/1.20      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.01/1.20      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.20  thf(t77_xboole_1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 1.01/1.20          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 1.01/1.20  thf('16', plain,
% 1.01/1.20      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.01/1.20         ((r1_xboole_0 @ X12 @ X13)
% 1.01/1.20          | ~ (r1_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 1.01/1.20          | ~ (r1_tarski @ X12 @ X14))),
% 1.01/1.20      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.01/1.20  thf('17', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         (~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.01/1.20          | ~ (r1_tarski @ X2 @ X1)
% 1.01/1.20          | (r1_xboole_0 @ X2 @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['15', '16'])).
% 1.01/1.20  thf('18', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.01/1.20          | (r1_xboole_0 @ X0 @ sk_C)
% 1.01/1.20          | ~ (r1_tarski @ X0 @ sk_B))),
% 1.01/1.20      inference('sup-', [status(thm)], ['14', '17'])).
% 1.01/1.20  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.01/1.20  thf('19', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 1.01/1.20      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.01/1.20  thf('20', plain,
% 1.01/1.20      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_C) | ~ (r1_tarski @ X0 @ sk_B))),
% 1.01/1.20      inference('demod', [status(thm)], ['18', '19'])).
% 1.01/1.20  thf('21', plain,
% 1.01/1.20      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.01/1.20        | (r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['9', '20'])).
% 1.01/1.20  thf(l24_zfmisc_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 1.01/1.20  thf('22', plain,
% 1.01/1.20      (![X24 : $i, X25 : $i]:
% 1.01/1.20         (~ (r1_xboole_0 @ (k1_tarski @ X24) @ X25) | ~ (r2_hidden @ X24 @ X25))),
% 1.01/1.20      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 1.01/1.20  thf('23', plain,
% 1.01/1.20      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.01/1.20        | ~ (r2_hidden @ sk_D @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['21', '22'])).
% 1.01/1.20  thf('24', plain, ((r2_hidden @ sk_D @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('25', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.01/1.20      inference('demod', [status(thm)], ['23', '24'])).
% 1.01/1.20  thf('26', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 1.01/1.20      inference('demod', [status(thm)], ['12', '13'])).
% 1.01/1.20  thf('27', plain,
% 1.01/1.20      (![X4 : $i, X6 : $i]:
% 1.01/1.20         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.01/1.20      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.01/1.20  thf('28', plain,
% 1.01/1.20      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['26', '27'])).
% 1.01/1.20  thf('29', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 1.01/1.20      inference('simplify', [status(thm)], ['28'])).
% 1.01/1.20  thf(t78_xboole_1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ( r1_xboole_0 @ A @ B ) =>
% 1.01/1.20       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.01/1.20         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.01/1.20  thf('30', plain,
% 1.01/1.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.01/1.20         (~ (r1_xboole_0 @ X15 @ X16)
% 1.01/1.20          | ((k3_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.01/1.20              = (k3_xboole_0 @ X15 @ X17)))),
% 1.01/1.20      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.01/1.20  thf('31', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))
% 1.01/1.20           = (k3_xboole_0 @ sk_B @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['29', '30'])).
% 1.01/1.20  thf('32', plain,
% 1.01/1.20      (![X4 : $i, X6 : $i]:
% 1.01/1.20         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.01/1.20      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.01/1.20  thf('33', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 1.01/1.20          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['31', '32'])).
% 1.01/1.20  thf('34', plain,
% 1.01/1.20      ((((k1_xboole_0) != (k1_xboole_0))
% 1.01/1.20        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['25', '33'])).
% 1.01/1.20  thf('35', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A))),
% 1.01/1.20      inference('simplify', [status(thm)], ['34'])).
% 1.01/1.20  thf(symmetry_r1_xboole_0, axiom,
% 1.01/1.20    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.01/1.20  thf('36', plain,
% 1.01/1.20      (![X7 : $i, X8 : $i]:
% 1.01/1.20         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.01/1.20      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.01/1.20  thf('37', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_B)),
% 1.01/1.20      inference('sup-', [status(thm)], ['35', '36'])).
% 1.01/1.20  thf('38', plain, ($false), inference('demod', [status(thm)], ['2', '37'])).
% 1.01/1.20  
% 1.01/1.20  % SZS output end Refutation
% 1.01/1.20  
% 1.04/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
