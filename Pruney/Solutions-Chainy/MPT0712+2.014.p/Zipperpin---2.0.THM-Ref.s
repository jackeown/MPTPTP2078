%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7znnpbZ7g3

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  87 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  368 ( 711 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t167_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t167_funct_1])).

thf('1',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X4 ) @ X5 )
      | ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k7_relat_1 @ X13 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ ( k2_tarski @ X6 @ X9 ) )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('13',plain,(
    ! [X6: $i,X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X6 @ X9 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','14','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','14','15'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ( ( k9_relat_1 @ X15 @ ( k2_tarski @ X14 @ X16 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X15 @ X14 ) @ ( k1_funct_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['4','26','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7znnpbZ7g3
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 32 iterations in 0.021s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(t148_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]:
% 0.20/0.47         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.20/0.47          | ~ (v1_relat_1 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.47  thf(t167_funct_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47       ( r1_tarski @
% 0.20/0.47         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.20/0.47         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47          ( r1_tarski @
% 0.20/0.47            ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.20/0.47            ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t167_funct_1])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (~ (r1_tarski @ 
% 0.20/0.47          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.20/0.47          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.20/0.47           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.20/0.47          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(l27_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ (k1_tarski @ X4) @ X5) | (r2_hidden @ X4 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.47  thf(t187_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.47           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         (~ (r1_xboole_0 @ X12 @ (k1_relat_1 @ X13))
% 0.20/0.47          | ((k7_relat_1 @ X13 @ X12) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ((k7_relat_1 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (~ (r1_tarski @ 
% 0.20/0.47          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.20/0.47          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.20/0.47           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf(t60_relat_1, axiom,
% 0.20/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('10', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.47  thf(t69_enumset1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.47  thf('11', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf(l45_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.20/0.47       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.20/0.47            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         ((r1_tarski @ X8 @ (k2_tarski @ X6 @ X9)) | ((X8) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X6 : $i, X9 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X6 @ X9))),
% 0.20/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.47  thf('14', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['11', '13'])).
% 0.20/0.47  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('16', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10', '14', '15'])).
% 0.20/0.47  thf('17', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10', '14', '15'])).
% 0.20/0.47  thf(t118_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.47           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.20/0.47         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.47           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.20/0.47          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.20/0.47          | ((k9_relat_1 @ X15 @ (k2_tarski @ X14 @ X16))
% 0.20/0.47              = (k2_tarski @ (k1_funct_1 @ X15 @ X14) @ 
% 0.20/0.47                 (k1_funct_1 @ X15 @ X16)))
% 0.20/0.47          | ~ (v1_funct_1 @ X15)
% 0.20/0.47          | ~ (v1_relat_1 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ sk_B)
% 0.20/0.47          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47          | ((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.20/0.47              = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.20/0.47                 (k1_funct_1 @ sk_B @ X0)))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.20/0.47            = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.20/0.47               (k1_funct_1 @ sk_B @ X0)))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 0.20/0.47         = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '22'])).
% 0.20/0.47  thf('24', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf('25', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.47         = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('28', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.47      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.47  thf('29', plain, ($false),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '26', '28'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
