%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UTIGAJWNwf

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:51 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   53 (  80 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  261 ( 478 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(fc16_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ~ ( v1_xboole_0 @ X56 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X55 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[fc16_relat_1])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('2',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X58 @ X59 ) @ X60 )
        = ( k7_relat_1 @ X58 @ ( k3_xboole_0 @ X59 @ X60 ) ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t207_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_xboole_0 @ A @ B )
         => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t207_relat_1])).

thf('5',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ( k7_relat_1 @ sk_C @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['6','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_C @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,
    ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_C @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X11 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_C @ k1_xboole_0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['13','25'])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['24'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UTIGAJWNwf
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 290 iterations in 0.152s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.37/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.61  thf(fc16_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_xboole_0 @ B ) ) =>
% 0.37/0.61       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.37/0.61         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (![X55 : $i, X56 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X55)
% 0.37/0.61          | ~ (v1_xboole_0 @ X56)
% 0.37/0.61          | (v1_xboole_0 @ (k7_relat_1 @ X55 @ X56)))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc16_relat_1])).
% 0.37/0.61  thf(t6_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [t6_boole])).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [t6_boole])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf(t100_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ C ) =>
% 0.37/0.61       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.37/0.61         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.37/0.61         (((k7_relat_1 @ (k7_relat_1 @ X58 @ X59) @ X60)
% 0.37/0.61            = (k7_relat_1 @ X58 @ (k3_xboole_0 @ X59 @ X60)))
% 0.37/0.61          | ~ (v1_relat_1 @ X58))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.37/0.61  thf(t207_relat_1, conjecture,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ C ) =>
% 0.37/0.61       ( ( r1_xboole_0 @ A @ B ) =>
% 0.37/0.61         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.61        ( ( v1_relat_1 @ C ) =>
% 0.37/0.61          ( ( r1_xboole_0 @ A @ B ) =>
% 0.37/0.61            ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t207_relat_1])).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      ((((k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) != (k1_xboole_0))
% 0.37/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.61  thf('7', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(d7_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.61  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.61  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('11', plain, (((k7_relat_1 @ sk_C @ k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['6', '9', '10'])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((X0) != (k1_xboole_0))
% 0.37/0.61          | ~ (v1_xboole_0 @ X0)
% 0.37/0.61          | ~ (v1_xboole_0 @ (k7_relat_1 @ sk_C @ k1_xboole_0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['3', '11'])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      ((~ (v1_xboole_0 @ (k7_relat_1 @ sk_C @ k1_xboole_0))
% 0.37/0.61        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.61      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.61  thf(t61_xboole_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X11 : $i]:
% 0.37/0.61         ((r2_xboole_0 @ k1_xboole_0 @ X11) | ((X11) = (k1_xboole_0)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.37/0.61  thf(d8_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.37/0.61       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ~ (r2_xboole_0 @ X3 @ X4))),
% 0.37/0.61      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.61  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.61  thf('17', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.37/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.61  thf(symmetry_r1_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i]:
% 0.37/0.61         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.61  thf('19', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.61  thf(t69_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.61       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (![X13 : $i, X14 : $i]:
% 0.37/0.61         (~ (r1_xboole_0 @ X13 @ X14)
% 0.37/0.61          | ~ (r1_tarski @ X13 @ X14)
% 0.37/0.61          | (v1_xboole_0 @ X13))),
% 0.37/0.61      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['16', '21'])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.61  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.61  thf('26', plain, (~ (v1_xboole_0 @ (k7_relat_1 @ sk_C @ k1_xboole_0))),
% 0.37/0.61      inference('simplify_reflect+', [status(thm)], ['13', '25'])).
% 0.37/0.61  thf('27', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['0', '26'])).
% 0.37/0.61  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.61  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('30', plain, ($false),
% 0.37/0.61      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
