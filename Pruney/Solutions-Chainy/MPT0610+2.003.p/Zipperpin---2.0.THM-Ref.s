%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YGSokPnwvd

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:04 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  301 ( 443 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t214_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t214_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('2',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X23 @ X22 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X23 ) @ ( k1_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t14_relat_1])).

thf('6',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    = ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','15'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('17',plain,(
    ! [X24: $i] :
      ( ( ( k3_xboole_0 @ X24 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X24 ) @ ( k2_relat_1 @ X24 ) ) )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,(
    ! [X17: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('23',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','20','21','22'])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YGSokPnwvd
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:14:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 80 iterations in 0.035s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(t214_relat_1, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( v1_relat_1 @ B ) =>
% 0.19/0.48           ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.48             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( v1_relat_1 @ A ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( v1_relat_1 @ B ) =>
% 0.19/0.48              ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.48                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t214_relat_1])).
% 0.19/0.48  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(fc1_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X20 : $i, X21 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.19/0.48  thf('2', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d7_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.48       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.19/0.48         = (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf(t14_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( v1_relat_1 @ B ) =>
% 0.19/0.48           ( r1_tarski @
% 0.19/0.48             ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.19/0.48             ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X22 : $i, X23 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X22)
% 0.19/0.48          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X23 @ X22)) @ 
% 0.19/0.48             (k3_xboole_0 @ (k1_relat_1 @ X23) @ (k1_relat_1 @ X22)))
% 0.19/0.48          | ~ (v1_relat_1 @ X23))),
% 0.19/0.48      inference('cnf', [status(esa)], [t14_relat_1])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ k1_xboole_0)
% 0.19/0.48        | ~ (v1_relat_1 @ sk_A)
% 0.19/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ k1_xboole_0)),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.19/0.48  thf(t28_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (((k3_xboole_0 @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ k1_xboole_0)
% 0.19/0.48         = (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.48  thf(t2_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (((k1_xboole_0) = (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.19/0.48  thf(t22_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ( k3_xboole_0 @
% 0.19/0.48           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.19/0.48         ( A ) ) ))).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X24 : $i]:
% 0.19/0.48         (((k3_xboole_0 @ X24 @ 
% 0.19/0.48            (k2_zfmisc_1 @ (k1_relat_1 @ X24) @ (k2_relat_1 @ X24))) = (
% 0.19/0.48            X24))
% 0.19/0.48          | ~ (v1_relat_1 @ X24))),
% 0.19/0.48      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.19/0.48          (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.19/0.48           (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))))
% 0.19/0.48          = (k3_xboole_0 @ sk_A @ sk_B))
% 0.19/0.48        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf(t113_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i]:
% 0.19/0.48         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 0.19/0.48          | ((X16) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X17 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))
% 0.19/0.48        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['18', '20', '21', '22'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ sk_A) | ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '23'])).
% 0.19/0.48  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('26', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X2 : $i, X4 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.19/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.19/0.48  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
