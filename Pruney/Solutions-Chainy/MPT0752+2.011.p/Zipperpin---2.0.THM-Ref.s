%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U2ICpQk7PE

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  54 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  204 ( 241 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t45_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v5_ordinal1 @ k1_xboole_0 )
        & ( v1_funct_1 @ k1_xboole_0 )
        & ( v5_relat_1 @ k1_xboole_0 @ A )
        & ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t45_ordinal1])).

thf('0',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('1',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('3',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('5',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','3','4'])).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('7',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(rc3_ordinal1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v5_ordinal1 @ B )
      & ( v1_funct_1 @ B )
      & ( v5_relat_1 @ B @ A )
      & ( v1_relat_1 @ B ) ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( v5_relat_1 @ ( sk_B @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( sk_B @ X12 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X9: $i] :
      ( ( ( k2_relat_1 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( sk_B @ X12 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X12: $i] :
      ( v5_ordinal1 @ ( sk_B @ X12 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('25',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['9','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U2ICpQk7PE
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 40 iterations in 0.016s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(t45_ordinal1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.21/0.47       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.21/0.47          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.21/0.47        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.47        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.47  thf('1', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.47  thf(fc3_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('2', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.47  thf('3', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(l222_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.21/0.47  thf('4', plain, (![X7 : $i]: (v5_relat_1 @ k1_xboole_0 @ X7)),
% 0.21/0.47      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((~ (v5_ordinal1 @ k1_xboole_0) | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '3', '4'])).
% 0.21/0.47  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.47  thf('7', plain, (![X11 : $i]: (v1_funct_1 @ (k6_relat_1 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.47  thf('8', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain, (~ (v5_ordinal1 @ k1_xboole_0)),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.47  thf(rc3_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ?[B:$i]:
% 0.21/0.47       ( ( v5_ordinal1 @ B ) & ( v1_funct_1 @ B ) & ( v5_relat_1 @ B @ A ) & 
% 0.21/0.47         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.47  thf('10', plain, (![X12 : $i]: (v5_relat_1 @ (sk_B @ X12) @ X12)),
% 0.21/0.47      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.21/0.47  thf(d19_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (v5_relat_1 @ X5 @ X6)
% 0.21/0.47          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.21/0.47          | ~ (v1_relat_1 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.47          | (r1_tarski @ (k2_relat_1 @ (sk_B @ X0)) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain, (![X12 : $i]: (v1_relat_1 @ (sk_B @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.21/0.47  thf('14', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (sk_B @ X0)) @ X0)),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.47  thf('15', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf(d10_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i, X2 : $i]:
% 0.21/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.47  thf(t64_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.47         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X9 : $i]:
% 0.21/0.47         (((k2_relat_1 @ X9) != (k1_xboole_0))
% 0.21/0.47          | ((X9) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.21/0.48        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain, (![X12 : $i]: (v1_relat_1 @ (sk_B @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.48  thf('24', plain, (![X12 : $i]: (v5_ordinal1 @ (sk_B @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.21/0.48  thf('25', plain, ((v5_ordinal1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain, ($false), inference('demod', [status(thm)], ['9', '25'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
