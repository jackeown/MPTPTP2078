%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6HC2z22La

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:28 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   57 (  69 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  332 ( 498 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf('1',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X42
        = ( k1_tarski @ X41 ) )
      | ( X42 = k1_xboole_0 )
      | ~ ( r1_tarski @ X42 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ X8 )
      | ( r1_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_C )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('18',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X46 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r2_hidden @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['24'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
        = ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf('33',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6HC2z22La
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:39:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.72/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.72/0.88  % Solved by: fo/fo7.sh
% 0.72/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.88  % done 2086 iterations in 0.420s
% 0.72/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.72/0.88  % SZS output start Refutation
% 0.72/0.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.72/0.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.72/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.88  thf(sk_D_type, type, sk_D: $i).
% 0.72/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.72/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.72/0.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.72/0.88  thf(t149_zfmisc_1, conjecture,
% 0.72/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.88     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.72/0.88         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.72/0.88       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.72/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.88    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.88        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.72/0.88            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.72/0.88          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.72/0.88    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.72/0.88  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('1', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf(d7_xboole_0, axiom,
% 0.72/0.88    (![A:$i,B:$i]:
% 0.72/0.88     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.72/0.88       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.72/0.88  thf('2', plain,
% 0.72/0.88      (![X2 : $i, X3 : $i]:
% 0.72/0.88         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.72/0.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.72/0.88  thf('3', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.72/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.72/0.88  thf(commutativity_k3_xboole_0, axiom,
% 0.72/0.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.72/0.88  thf('4', plain,
% 0.72/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.88  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.72/0.88      inference('demod', [status(thm)], ['3', '4'])).
% 0.72/0.88  thf('6', plain,
% 0.72/0.88      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('7', plain,
% 0.72/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.88  thf('8', plain,
% 0.72/0.88      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.72/0.88      inference('demod', [status(thm)], ['6', '7'])).
% 0.72/0.88  thf(l3_zfmisc_1, axiom,
% 0.72/0.88    (![A:$i,B:$i]:
% 0.72/0.88     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.72/0.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.72/0.88  thf('9', plain,
% 0.72/0.88      (![X41 : $i, X42 : $i]:
% 0.72/0.88         (((X42) = (k1_tarski @ X41))
% 0.72/0.88          | ((X42) = (k1_xboole_0))
% 0.72/0.88          | ~ (r1_tarski @ X42 @ (k1_tarski @ X41)))),
% 0.72/0.88      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.72/0.88  thf('10', plain,
% 0.72/0.88      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.72/0.88        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D)))),
% 0.72/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.72/0.88  thf('11', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf(t74_xboole_1, axiom,
% 0.72/0.88    (![A:$i,B:$i,C:$i]:
% 0.72/0.88     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.72/0.88          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.72/0.88  thf('12', plain,
% 0.72/0.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.72/0.88         (~ (r1_xboole_0 @ X7 @ X8)
% 0.72/0.88          | (r1_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.72/0.88      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.72/0.88  thf('13', plain,
% 0.72/0.88      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ X0))),
% 0.72/0.88      inference('sup-', [status(thm)], ['11', '12'])).
% 0.72/0.88  thf(symmetry_r1_xboole_0, axiom,
% 0.72/0.88    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.72/0.88  thf('14', plain,
% 0.72/0.88      (![X5 : $i, X6 : $i]:
% 0.72/0.88         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.72/0.88      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.72/0.88  thf('15', plain,
% 0.72/0.88      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C)),
% 0.72/0.88      inference('sup-', [status(thm)], ['13', '14'])).
% 0.72/0.88  thf('16', plain,
% 0.72/0.88      (((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_C)
% 0.72/0.88        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.72/0.88      inference('sup+', [status(thm)], ['10', '15'])).
% 0.72/0.88  thf(t69_enumset1, axiom,
% 0.72/0.88    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.72/0.88  thf('17', plain,
% 0.72/0.88      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.72/0.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.72/0.88  thf(t55_zfmisc_1, axiom,
% 0.72/0.88    (![A:$i,B:$i,C:$i]:
% 0.72/0.88     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.72/0.88  thf('18', plain,
% 0.72/0.88      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.72/0.88         (~ (r1_xboole_0 @ (k2_tarski @ X46 @ X47) @ X48)
% 0.72/0.88          | ~ (r2_hidden @ X46 @ X48))),
% 0.72/0.88      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.72/0.88  thf('19', plain,
% 0.72/0.88      (![X0 : $i, X1 : $i]:
% 0.72/0.88         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.72/0.88      inference('sup-', [status(thm)], ['17', '18'])).
% 0.72/0.88  thf('20', plain,
% 0.72/0.88      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.72/0.88        | ~ (r2_hidden @ sk_D @ sk_C))),
% 0.72/0.88      inference('sup-', [status(thm)], ['16', '19'])).
% 0.72/0.88  thf('21', plain, ((r2_hidden @ sk_D @ sk_C)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('22', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.72/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.72/0.88  thf('23', plain,
% 0.72/0.88      (![X2 : $i, X4 : $i]:
% 0.72/0.88         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.72/0.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.72/0.88  thf('24', plain,
% 0.72/0.88      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.72/0.88      inference('sup-', [status(thm)], ['22', '23'])).
% 0.72/0.88  thf('25', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.72/0.88      inference('simplify', [status(thm)], ['24'])).
% 0.72/0.88  thf(t78_xboole_1, axiom,
% 0.72/0.88    (![A:$i,B:$i,C:$i]:
% 0.72/0.88     ( ( r1_xboole_0 @ A @ B ) =>
% 0.72/0.88       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.72/0.88         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.72/0.88  thf('26', plain,
% 0.72/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.72/0.88         (~ (r1_xboole_0 @ X10 @ X11)
% 0.72/0.88          | ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.72/0.88              = (k3_xboole_0 @ X10 @ X12)))),
% 0.72/0.88      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.72/0.88  thf('27', plain,
% 0.72/0.88      (![X0 : $i]:
% 0.72/0.88         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 0.72/0.88           = (k3_xboole_0 @ sk_B @ X0))),
% 0.72/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.72/0.88  thf('28', plain,
% 0.72/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.88  thf('29', plain,
% 0.72/0.88      (![X2 : $i, X4 : $i]:
% 0.72/0.88         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.72/0.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.72/0.88  thf('30', plain,
% 0.72/0.88      (![X0 : $i, X1 : $i]:
% 0.72/0.88         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.72/0.88      inference('sup-', [status(thm)], ['28', '29'])).
% 0.72/0.88  thf('31', plain,
% 0.72/0.88      (![X0 : $i]:
% 0.72/0.88         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 0.72/0.88          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.72/0.88      inference('sup-', [status(thm)], ['27', '30'])).
% 0.72/0.88  thf('32', plain,
% 0.72/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.88        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.72/0.88      inference('sup-', [status(thm)], ['5', '31'])).
% 0.72/0.88  thf('33', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.72/0.88      inference('simplify', [status(thm)], ['32'])).
% 0.72/0.88  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.72/0.88  
% 0.72/0.88  % SZS output end Refutation
% 0.72/0.88  
% 0.72/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
