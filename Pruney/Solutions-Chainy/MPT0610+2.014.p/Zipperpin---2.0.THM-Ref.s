%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IsreEAqIDR

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  68 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   19
%              Number of atoms          :  310 ( 474 expanded)
%              Number of equality atoms :   27 (  28 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

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
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('4',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X13 @ X12 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t14_relat_1])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('13',plain,
    ( ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X14 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X10 ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('21',plain,
    ( ( ( k8_relat_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k8_relat_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k8_relat_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t137_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X11: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf('26',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IsreEAqIDR
% 0.14/0.37  % Computer   : n006.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 20:47:08 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 31 iterations in 0.012s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.45  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.45  thf(t214_relat_1, conjecture,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ A ) =>
% 0.22/0.45       ( ![B:$i]:
% 0.22/0.45         ( ( v1_relat_1 @ B ) =>
% 0.22/0.45           ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.45             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i]:
% 0.22/0.45        ( ( v1_relat_1 @ A ) =>
% 0.22/0.45          ( ![B:$i]:
% 0.22/0.45            ( ( v1_relat_1 @ B ) =>
% 0.22/0.45              ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.45                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t214_relat_1])).
% 0.22/0.45  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(fc1_relat_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      (![X8 : $i, X9 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ X8) | (v1_relat_1 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.22/0.45      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.22/0.45  thf('2', plain,
% 0.22/0.45      (![X8 : $i, X9 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ X8) | (v1_relat_1 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.22/0.45      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.22/0.45  thf('3', plain,
% 0.22/0.45      (![X8 : $i, X9 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ X8) | (v1_relat_1 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.22/0.45      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.22/0.45  thf('4', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(d7_xboole_0, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.45       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.45  thf('5', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.45      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.45  thf('6', plain,
% 0.22/0.45      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.22/0.45         = (k1_xboole_0))),
% 0.22/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.45  thf(t14_relat_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ A ) =>
% 0.22/0.45       ( ![B:$i]:
% 0.22/0.45         ( ( v1_relat_1 @ B ) =>
% 0.22/0.45           ( r1_tarski @
% 0.22/0.45             ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.22/0.45             ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.22/0.45  thf('7', plain,
% 0.22/0.45      (![X12 : $i, X13 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ X12)
% 0.22/0.45          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X13 @ X12)) @ 
% 0.22/0.45             (k3_xboole_0 @ (k1_relat_1 @ X13) @ (k1_relat_1 @ X12)))
% 0.22/0.45          | ~ (v1_relat_1 @ X13))),
% 0.22/0.45      inference('cnf', [status(esa)], [t14_relat_1])).
% 0.22/0.45  thf('8', plain,
% 0.22/0.45      (((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ k1_xboole_0)
% 0.22/0.45        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.45        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.45      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.45  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('11', plain,
% 0.22/0.45      ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ k1_xboole_0)),
% 0.22/0.45      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.22/0.45  thf(t3_xboole_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.45  thf('12', plain,
% 0.22/0.45      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.22/0.45      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.45  thf('13', plain,
% 0.22/0.45      (((k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.22/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.45  thf(t65_relat_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ A ) =>
% 0.22/0.45       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.45         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.45  thf('14', plain,
% 0.22/0.45      (![X14 : $i]:
% 0.22/0.45         (((k1_relat_1 @ X14) != (k1_xboole_0))
% 0.22/0.45          | ((k2_relat_1 @ X14) = (k1_xboole_0))
% 0.22/0.45          | ~ (v1_relat_1 @ X14))),
% 0.22/0.45      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.22/0.45  thf('15', plain,
% 0.22/0.45      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.45        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.22/0.45        | ((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.45  thf('16', plain,
% 0.22/0.45      ((((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.22/0.45        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.45      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.45  thf('17', plain,
% 0.22/0.45      ((~ (v1_relat_1 @ sk_A)
% 0.22/0.45        | ((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['3', '16'])).
% 0.22/0.45  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('19', plain,
% 0.22/0.45      (((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.22/0.45      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.45  thf(t126_relat_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ A ) =>
% 0.22/0.45       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.22/0.45  thf('20', plain,
% 0.22/0.45      (![X10 : $i]:
% 0.22/0.45         (((k8_relat_1 @ (k2_relat_1 @ X10) @ X10) = (X10))
% 0.22/0.45          | ~ (v1_relat_1 @ X10))),
% 0.22/0.45      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.22/0.45  thf('21', plain,
% 0.22/0.45      ((((k8_relat_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.22/0.45          = (k3_xboole_0 @ sk_A @ sk_B))
% 0.22/0.45        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.45      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.45  thf('22', plain,
% 0.22/0.45      ((~ (v1_relat_1 @ sk_A)
% 0.22/0.45        | ((k8_relat_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.22/0.45            = (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['2', '21'])).
% 0.22/0.45  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('24', plain,
% 0.22/0.45      (((k8_relat_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.22/0.45         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.45      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.45  thf(t137_relat_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ A ) =>
% 0.22/0.45       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.45  thf('25', plain,
% 0.22/0.45      (![X11 : $i]:
% 0.22/0.45         (((k8_relat_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))
% 0.22/0.45          | ~ (v1_relat_1 @ X11))),
% 0.22/0.45      inference('cnf', [status(esa)], [t137_relat_1])).
% 0.22/0.45  thf('26', plain,
% 0.22/0.45      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.45        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.45      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.45  thf('27', plain,
% 0.22/0.45      ((~ (v1_relat_1 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['1', '26'])).
% 0.22/0.45  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('29', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.45      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.45  thf('30', plain,
% 0.22/0.45      (![X0 : $i, X2 : $i]:
% 0.22/0.45         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.22/0.45      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.45  thf('31', plain,
% 0.22/0.45      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.45      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.45  thf('32', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.22/0.45      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.45  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
