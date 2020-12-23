%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XRi7tIm8oT

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  243 ( 297 expanded)
%              Number of equality atoms :   28 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('3',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X3 ) ),
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
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
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
    ! [X9: $i] :
      ( v5_relat_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v5_relat_1 @ X1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( sk_B @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('16',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t197_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( ( k2_relat_1 @ A )
                = k1_xboole_0 )
              & ( ( k2_relat_1 @ B )
                = k1_xboole_0 ) )
           => ( A = B ) ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( X6 = X5 )
      | ( ( k2_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X6 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t197_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( sk_B @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X9: $i] :
      ( v5_ordinal1 @ ( sk_B @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('28',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['9','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XRi7tIm8oT
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 34 iterations in 0.014s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(t45_ordinal1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.20/0.46       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.20/0.46          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.20/0.46        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.46        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.46        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.46  thf('1', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.46  thf(fc3_funct_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.46  thf('2', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.46  thf('3', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(l222_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.20/0.46  thf('4', plain, (![X3 : $i]: (v5_relat_1 @ k1_xboole_0 @ X3)),
% 0.20/0.46      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      ((~ (v5_ordinal1 @ k1_xboole_0) | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '3', '4'])).
% 0.20/0.46  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.46  thf('7', plain, (![X8 : $i]: (v1_funct_1 @ (k6_relat_1 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.46  thf('8', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, (~ (v5_ordinal1 @ k1_xboole_0)),
% 0.20/0.46      inference('demod', [status(thm)], ['5', '8'])).
% 0.20/0.46  thf(rc3_ordinal1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ?[B:$i]:
% 0.20/0.46       ( ( v5_ordinal1 @ B ) & ( v1_funct_1 @ B ) & ( v5_relat_1 @ B @ A ) & 
% 0.20/0.46         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.46  thf('10', plain, (![X9 : $i]: (v5_relat_1 @ (sk_B @ X9) @ X9)),
% 0.20/0.46      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.46  thf(d19_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v5_relat_1 @ X1 @ X2)
% 0.20/0.46          | (r1_tarski @ (k2_relat_1 @ X1) @ X2)
% 0.20/0.46          | ~ (v1_relat_1 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.46          | (r1_tarski @ (k2_relat_1 @ (sk_B @ X0)) @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('13', plain, (![X9 : $i]: (v1_relat_1 @ (sk_B @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.46  thf('14', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (sk_B @ X0)) @ X0)),
% 0.20/0.46      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.46  thf(t3_xboole_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.46  thf('16', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf(t60_relat_1, axiom,
% 0.20/0.46    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.46     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.46  thf('17', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.46  thf(t197_relat_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( v1_relat_1 @ B ) =>
% 0.20/0.46           ( ( ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.46               ( ( k2_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.46             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X5)
% 0.20/0.46          | ((X6) = (X5))
% 0.20/0.46          | ((k2_relat_1 @ X5) != (k1_xboole_0))
% 0.20/0.46          | ((k2_relat_1 @ X6) != (k1_xboole_0))
% 0.20/0.46          | ~ (v1_relat_1 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t197_relat_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.20/0.46          | ((X0) = (k1_xboole_0))
% 0.20/0.46          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.20/0.46          | ((X0) = (k1_xboole_0)))),
% 0.20/0.46      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((X0) = (k1_xboole_0))
% 0.20/0.46          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.20/0.46        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['16', '22'])).
% 0.20/0.46  thf('24', plain, (![X9 : $i]: (v1_relat_1 @ (sk_B @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.46      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.46  thf('26', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.46  thf('27', plain, (![X9 : $i]: (v5_ordinal1 @ (sk_B @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.46  thf('28', plain, ((v5_ordinal1 @ k1_xboole_0)),
% 0.20/0.46      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain, ($false), inference('demod', [status(thm)], ['9', '28'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
