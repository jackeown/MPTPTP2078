%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PMNgNWABCv

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:05 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   41 (  53 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  233 ( 367 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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
    ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('3',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X40 @ X39 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X40 ) @ ( k1_relat_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t14_relat_1])).

thf('7',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('11',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X52 ) @ X53 )
      | ( ( k7_relat_1 @ X52 @ X53 )
        = X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    | ( ( k7_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k7_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k7_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PMNgNWABCv
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.47/1.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.47/1.65  % Solved by: fo/fo7.sh
% 1.47/1.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.47/1.65  % done 1749 iterations in 1.195s
% 1.47/1.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.47/1.65  % SZS output start Refutation
% 1.47/1.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.47/1.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.47/1.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.47/1.65  thf(sk_A_type, type, sk_A: $i).
% 1.47/1.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.47/1.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.47/1.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.47/1.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.47/1.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.47/1.65  thf(t214_relat_1, conjecture,
% 1.47/1.65    (![A:$i]:
% 1.47/1.65     ( ( v1_relat_1 @ A ) =>
% 1.47/1.65       ( ![B:$i]:
% 1.47/1.65         ( ( v1_relat_1 @ B ) =>
% 1.47/1.65           ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 1.47/1.65             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 1.47/1.65  thf(zf_stmt_0, negated_conjecture,
% 1.47/1.65    (~( ![A:$i]:
% 1.47/1.65        ( ( v1_relat_1 @ A ) =>
% 1.47/1.65          ( ![B:$i]:
% 1.47/1.65            ( ( v1_relat_1 @ B ) =>
% 1.47/1.65              ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 1.47/1.65                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 1.47/1.65    inference('cnf.neg', [status(esa)], [t214_relat_1])).
% 1.47/1.65  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B_1)),
% 1.47/1.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.65  thf(fc1_relat_1, axiom,
% 1.47/1.65    (![A:$i,B:$i]:
% 1.47/1.65     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.47/1.65  thf('1', plain,
% 1.47/1.65      (![X30 : $i, X31 : $i]:
% 1.47/1.65         (~ (v1_relat_1 @ X30) | (v1_relat_1 @ (k3_xboole_0 @ X30 @ X31)))),
% 1.47/1.65      inference('cnf', [status(esa)], [fc1_relat_1])).
% 1.47/1.65  thf('2', plain,
% 1.47/1.65      (![X30 : $i, X31 : $i]:
% 1.47/1.65         (~ (v1_relat_1 @ X30) | (v1_relat_1 @ (k3_xboole_0 @ X30 @ X31)))),
% 1.47/1.65      inference('cnf', [status(esa)], [fc1_relat_1])).
% 1.47/1.65  thf('3', plain,
% 1.47/1.65      ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))),
% 1.47/1.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.65  thf(d7_xboole_0, axiom,
% 1.47/1.65    (![A:$i,B:$i]:
% 1.47/1.65     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.47/1.65       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.47/1.65  thf('4', plain,
% 1.47/1.65      (![X0 : $i, X1 : $i]:
% 1.47/1.65         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.47/1.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.47/1.65  thf('5', plain,
% 1.47/1.65      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))
% 1.47/1.65         = (k1_xboole_0))),
% 1.47/1.65      inference('sup-', [status(thm)], ['3', '4'])).
% 1.47/1.65  thf(t14_relat_1, axiom,
% 1.47/1.65    (![A:$i]:
% 1.47/1.65     ( ( v1_relat_1 @ A ) =>
% 1.47/1.65       ( ![B:$i]:
% 1.47/1.65         ( ( v1_relat_1 @ B ) =>
% 1.47/1.65           ( r1_tarski @
% 1.47/1.65             ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.47/1.65             ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.47/1.65  thf('6', plain,
% 1.47/1.65      (![X39 : $i, X40 : $i]:
% 1.47/1.65         (~ (v1_relat_1 @ X39)
% 1.47/1.65          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X40 @ X39)) @ 
% 1.47/1.65             (k3_xboole_0 @ (k1_relat_1 @ X40) @ (k1_relat_1 @ X39)))
% 1.47/1.65          | ~ (v1_relat_1 @ X40))),
% 1.47/1.65      inference('cnf', [status(esa)], [t14_relat_1])).
% 1.47/1.65  thf('7', plain,
% 1.47/1.65      (((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_1)) @ k1_xboole_0)
% 1.47/1.65        | ~ (v1_relat_1 @ sk_A)
% 1.47/1.65        | ~ (v1_relat_1 @ sk_B_1))),
% 1.47/1.65      inference('sup+', [status(thm)], ['5', '6'])).
% 1.47/1.65  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 1.47/1.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.65  thf('9', plain, ((v1_relat_1 @ sk_B_1)),
% 1.47/1.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.65  thf('10', plain,
% 1.47/1.65      ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_1)) @ k1_xboole_0)),
% 1.47/1.65      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.47/1.65  thf(t97_relat_1, axiom,
% 1.47/1.65    (![A:$i,B:$i]:
% 1.47/1.65     ( ( v1_relat_1 @ B ) =>
% 1.47/1.65       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.47/1.65         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.47/1.65  thf('11', plain,
% 1.47/1.65      (![X52 : $i, X53 : $i]:
% 1.47/1.65         (~ (r1_tarski @ (k1_relat_1 @ X52) @ X53)
% 1.47/1.65          | ((k7_relat_1 @ X52 @ X53) = (X52))
% 1.47/1.65          | ~ (v1_relat_1 @ X52))),
% 1.47/1.65      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.47/1.65  thf('12', plain,
% 1.47/1.65      ((~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_1))
% 1.47/1.65        | ((k7_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 1.47/1.65            = (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 1.47/1.65      inference('sup-', [status(thm)], ['10', '11'])).
% 1.47/1.65  thf('13', plain,
% 1.47/1.65      ((~ (v1_relat_1 @ sk_A)
% 1.47/1.65        | ((k7_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 1.47/1.65            = (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 1.47/1.65      inference('sup-', [status(thm)], ['2', '12'])).
% 1.47/1.65  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 1.47/1.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.65  thf('15', plain,
% 1.47/1.65      (((k7_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 1.47/1.65         = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 1.47/1.65      inference('demod', [status(thm)], ['13', '14'])).
% 1.47/1.65  thf(t110_relat_1, axiom,
% 1.47/1.65    (![A:$i]:
% 1.47/1.65     ( ( v1_relat_1 @ A ) =>
% 1.47/1.65       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 1.47/1.65  thf('16', plain,
% 1.47/1.65      (![X32 : $i]:
% 1.47/1.65         (((k7_relat_1 @ X32 @ k1_xboole_0) = (k1_xboole_0))
% 1.47/1.65          | ~ (v1_relat_1 @ X32))),
% 1.47/1.65      inference('cnf', [status(esa)], [t110_relat_1])).
% 1.47/1.65  thf('17', plain,
% 1.47/1.65      ((((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 1.47/1.65        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 1.47/1.65      inference('sup+', [status(thm)], ['15', '16'])).
% 1.47/1.65  thf('18', plain,
% 1.47/1.65      ((~ (v1_relat_1 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 1.47/1.65      inference('sup-', [status(thm)], ['1', '17'])).
% 1.47/1.65  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 1.47/1.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.65  thf('20', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 1.47/1.65      inference('demod', [status(thm)], ['18', '19'])).
% 1.47/1.65  thf('21', plain,
% 1.47/1.65      (![X0 : $i, X2 : $i]:
% 1.47/1.65         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 1.47/1.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.47/1.65  thf('22', plain,
% 1.47/1.65      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 1.47/1.65      inference('sup-', [status(thm)], ['20', '21'])).
% 1.47/1.65  thf('23', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 1.47/1.65      inference('simplify', [status(thm)], ['22'])).
% 1.47/1.65  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 1.47/1.65  
% 1.47/1.65  % SZS output end Refutation
% 1.47/1.65  
% 1.47/1.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
