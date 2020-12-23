%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EgTpP2ciRP

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 (  64 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 ( 357 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X43 ) @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ( k2_subset_1 @ X42 )
      = X42 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k4_subset_1 @ X46 @ X45 @ X47 )
        = ( k2_xboole_0 @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ X40 )
      | ( r2_hidden @ X39 @ X40 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X44: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X31 ) @ X33 )
      | ~ ( r2_hidden @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('13',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X36 ) @ ( k3_tarski @ X37 ) )
      | ~ ( r1_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('15',plain,(
    r1_tarski @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('21',plain,(
    ! [X38: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('22',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['15','20','21'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','24'])).

thf('26',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X42: $i] :
      ( ( k2_subset_1 @ X42 )
      = X42 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('28',plain,(
    ! [X42: $i] :
      ( ( k2_subset_1 @ X42 )
      = X42 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('29',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EgTpP2ciRP
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 60 iterations in 0.026s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.44  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.44  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.44  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.44  thf(dt_k2_subset_1, axiom,
% 0.19/0.44    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.44  thf('0', plain,
% 0.19/0.44      (![X43 : $i]: (m1_subset_1 @ (k2_subset_1 @ X43) @ (k1_zfmisc_1 @ X43))),
% 0.19/0.44      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.44  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.44  thf('1', plain, (![X42 : $i]: ((k2_subset_1 @ X42) = (X42))),
% 0.19/0.44      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.44  thf('2', plain, (![X43 : $i]: (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X43))),
% 0.19/0.44      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.44  thf(t28_subset_1, conjecture,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.44       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (~( ![A:$i,B:$i]:
% 0.19/0.44        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.44          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.19/0.44  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(redefinition_k4_subset_1, axiom,
% 0.19/0.44    (![A:$i,B:$i,C:$i]:
% 0.19/0.44     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.19/0.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.44       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.44  thf('4', plain,
% 0.19/0.44      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.19/0.44         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 0.19/0.44          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46))
% 0.19/0.44          | ((k4_subset_1 @ X46 @ X45 @ X47) = (k2_xboole_0 @ X45 @ X47)))),
% 0.19/0.44      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.19/0.44  thf('5', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.19/0.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.44  thf('6', plain,
% 0.19/0.44      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.44  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(d2_subset_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.44         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.44       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.44         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.44  thf('8', plain,
% 0.19/0.44      (![X39 : $i, X40 : $i]:
% 0.19/0.44         (~ (m1_subset_1 @ X39 @ X40)
% 0.19/0.44          | (r2_hidden @ X39 @ X40)
% 0.19/0.44          | (v1_xboole_0 @ X40))),
% 0.19/0.44      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.44  thf('9', plain,
% 0.19/0.44      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.44        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.44  thf(fc1_subset_1, axiom,
% 0.19/0.44    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.44  thf('10', plain, (![X44 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X44))),
% 0.19/0.44      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.44  thf('11', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.44      inference('clc', [status(thm)], ['9', '10'])).
% 0.19/0.44  thf(l1_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.44  thf('12', plain,
% 0.19/0.44      (![X31 : $i, X33 : $i]:
% 0.19/0.44         ((r1_tarski @ (k1_tarski @ X31) @ X33) | ~ (r2_hidden @ X31 @ X33))),
% 0.19/0.44      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.44  thf('13', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.44  thf(t95_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( r1_tarski @ A @ B ) =>
% 0.19/0.44       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.19/0.44  thf('14', plain,
% 0.19/0.44      (![X36 : $i, X37 : $i]:
% 0.19/0.44         ((r1_tarski @ (k3_tarski @ X36) @ (k3_tarski @ X37))
% 0.19/0.44          | ~ (r1_tarski @ X36 @ X37))),
% 0.19/0.44      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.19/0.44  thf('15', plain,
% 0.19/0.44      ((r1_tarski @ (k3_tarski @ (k1_tarski @ sk_B)) @ 
% 0.19/0.44        (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.44  thf(t69_enumset1, axiom,
% 0.19/0.44    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.44  thf('16', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.19/0.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.44  thf(l51_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.44  thf('17', plain,
% 0.19/0.44      (![X34 : $i, X35 : $i]:
% 0.19/0.44         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 0.19/0.44      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.44  thf('18', plain,
% 0.19/0.44      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.19/0.44      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.44  thf(idempotence_k2_xboole_0, axiom,
% 0.19/0.44    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.44  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.44      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.44  thf('20', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.19/0.44      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.44  thf(t99_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.19/0.44  thf('21', plain, (![X38 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X38)) = (X38))),
% 0.19/0.44      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.19/0.44  thf('22', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.44      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.19/0.44  thf(t12_xboole_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.44  thf('23', plain,
% 0.19/0.44      (![X1 : $i, X2 : $i]:
% 0.19/0.44         (((k2_xboole_0 @ X2 @ X1) = (X1)) | ~ (r1_tarski @ X2 @ X1))),
% 0.19/0.44      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.44  thf('24', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.44  thf('25', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['6', '24'])).
% 0.19/0.44  thf('26', plain,
% 0.19/0.44      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.19/0.44         != (k2_subset_1 @ sk_A))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('27', plain, (![X42 : $i]: ((k2_subset_1 @ X42) = (X42))),
% 0.19/0.44      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.44  thf('28', plain, (![X42 : $i]: ((k2_subset_1 @ X42) = (X42))),
% 0.19/0.44      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.44  thf('29', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.44  thf('30', plain, ($false),
% 0.19/0.44      inference('simplify_reflect-', [status(thm)], ['25', '29'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
