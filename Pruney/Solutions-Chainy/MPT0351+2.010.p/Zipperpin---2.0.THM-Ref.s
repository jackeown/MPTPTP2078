%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cCdOiFN7xN

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 (  68 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  325 ( 389 expanded)
%              Number of equality atoms :   32 (  39 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X45: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ X35 @ ( k3_tarski @ X36 ) )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('7',plain,(
    ! [X39: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['10','13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('22',plain,(
    ! [X43: $i] :
      ( ( k2_subset_1 @ X43 )
      = X43 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X43: $i] :
      ( ( k2_subset_1 @ X43 )
      = X43 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('24',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X44 ) @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('26',plain,(
    ! [X43: $i] :
      ( ( k2_subset_1 @ X43 )
      = X43 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) )
      | ( ( k4_subset_1 @ X47 @ X46 @ X48 )
        = ( k2_xboole_0 @ X46 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['24','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cCdOiFN7xN
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 51 iterations in 0.022s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(t28_subset_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i]:
% 0.19/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.19/0.47  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d2_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X40 : $i, X41 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X40 @ X41)
% 0.19/0.47          | (r2_hidden @ X40 @ X41)
% 0.19/0.47          | (v1_xboole_0 @ X41))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.47        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf(fc1_subset_1, axiom,
% 0.19/0.47    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.47  thf('3', plain, (![X45 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X45))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.47  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.47      inference('clc', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf(l49_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X35 : $i, X36 : $i]:
% 0.19/0.47         ((r1_tarski @ X35 @ (k3_tarski @ X36)) | ~ (r2_hidden @ X35 @ X36))),
% 0.19/0.47      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.19/0.47  thf('6', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf(t99_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.19/0.47  thf('7', plain, (![X39 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X39)) = (X39))),
% 0.19/0.47      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.19/0.47  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf(t28_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i]:
% 0.19/0.47         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.19/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.47  thf('10', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.47  thf(t22_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('14', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.47      inference('sup+', [status(thm)], ['10', '13'])).
% 0.19/0.47  thf(commutativity_k2_tarski, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.47  thf(l51_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X37 : $i, X38 : $i]:
% 0.19/0.47         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.19/0.47      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X37 : $i, X38 : $i]:
% 0.19/0.47         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.19/0.47      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('sup+', [status(thm)], ['17', '18'])).
% 0.19/0.47  thf('20', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['14', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.19/0.47         != (k2_subset_1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.47  thf('22', plain, (![X43 : $i]: ((k2_subset_1 @ X43) = (X43))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.47  thf('23', plain, (![X43 : $i]: ((k2_subset_1 @ X43) = (X43))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.47  thf('24', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.19/0.47  thf(dt_k2_subset_1, axiom,
% 0.19/0.47    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (![X44 : $i]: (m1_subset_1 @ (k2_subset_1 @ X44) @ (k1_zfmisc_1 @ X44))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.47  thf('26', plain, (![X43 : $i]: ((k2_subset_1 @ X43) = (X43))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.47  thf('27', plain, (![X44 : $i]: (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X44))),
% 0.19/0.47      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.47  thf('28', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(redefinition_k4_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.19/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.47       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.47  thf('29', plain,
% 0.19/0.47      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.19/0.47          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47))
% 0.19/0.47          | ((k4_subset_1 @ X47 @ X46 @ X48) = (k2_xboole_0 @ X46 @ X48)))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.19/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.47  thf('31', plain,
% 0.19/0.47      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['27', '30'])).
% 0.19/0.47  thf('32', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['24', '31'])).
% 0.19/0.47  thf('33', plain, ($false),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['20', '32'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
