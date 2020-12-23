%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F1oe8n97kH

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:09 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  303 ( 396 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ ( k1_relat_1 @ X37 ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t109_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X31 @ ( k6_subset_1 @ X32 @ X33 ) )
        = ( k6_subset_1 @ ( k7_relat_1 @ X31 @ X32 ) @ ( k7_relat_1 @ X31 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t109_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t216_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t216_relat_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r1_xboole_0 @ X22 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r1_xboole_0 @ X22 @ ( k6_subset_1 @ X24 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k6_subset_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k6_subset_1 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ X0 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r1_xboole_0 @ X22 @ ( k6_subset_1 @ X24 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_xboole_0 @ X34 @ X35 )
      | ~ ( v1_relat_1 @ X36 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X36 @ X34 ) @ X35 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C_2 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F1oe8n97kH
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:26 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.34  % Running portfolio for 600 s
% 0.21/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.48/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.66  % Solved by: fo/fo7.sh
% 0.48/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.66  % done 538 iterations in 0.209s
% 0.48/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.66  % SZS output start Refutation
% 0.48/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.66  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.48/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.48/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.66  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.48/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.66  thf(t98_relat_1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ A ) =>
% 0.48/0.66       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.48/0.66  thf('0', plain,
% 0.48/0.66      (![X37 : $i]:
% 0.48/0.66         (((k7_relat_1 @ X37 @ (k1_relat_1 @ X37)) = (X37))
% 0.48/0.66          | ~ (v1_relat_1 @ X37))),
% 0.48/0.66      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.48/0.66  thf(t109_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ C ) =>
% 0.48/0.66       ( ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.48/0.66         ( k6_subset_1 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.48/0.66  thf('1', plain,
% 0.48/0.66      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.48/0.66         (((k7_relat_1 @ X31 @ (k6_subset_1 @ X32 @ X33))
% 0.48/0.66            = (k6_subset_1 @ (k7_relat_1 @ X31 @ X32) @ 
% 0.48/0.66               (k7_relat_1 @ X31 @ X33)))
% 0.48/0.66          | ~ (v1_relat_1 @ X31))),
% 0.48/0.66      inference('cnf', [status(esa)], [t109_relat_1])).
% 0.48/0.66  thf('2', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k7_relat_1 @ X0 @ (k6_subset_1 @ (k1_relat_1 @ X0) @ X1))
% 0.48/0.66            = (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ X1)))
% 0.48/0.66          | ~ (v1_relat_1 @ X0)
% 0.48/0.66          | ~ (v1_relat_1 @ X0))),
% 0.48/0.66      inference('sup+', [status(thm)], ['0', '1'])).
% 0.48/0.66  thf('3', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X0)
% 0.48/0.66          | ((k7_relat_1 @ X0 @ (k6_subset_1 @ (k1_relat_1 @ X0) @ X1))
% 0.48/0.66              = (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ X1))))),
% 0.48/0.66      inference('simplify', [status(thm)], ['2'])).
% 0.48/0.66  thf(t216_relat_1, conjecture,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ C ) =>
% 0.48/0.66       ( ( r1_tarski @ A @ B ) =>
% 0.48/0.66         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.48/0.66           ( k1_xboole_0 ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.48/0.66        ( ( v1_relat_1 @ C ) =>
% 0.48/0.66          ( ( r1_tarski @ A @ B ) =>
% 0.48/0.66            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.48/0.66              ( k1_xboole_0 ) ) ) ) )),
% 0.48/0.66    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.48/0.66  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(t85_xboole_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.48/0.66  thf('5', plain,
% 0.48/0.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.48/0.66         (~ (r1_tarski @ X22 @ X23)
% 0.48/0.66          | (r1_xboole_0 @ X22 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.48/0.66  thf(redefinition_k6_subset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.48/0.66  thf('6', plain,
% 0.48/0.66      (![X27 : $i, X28 : $i]:
% 0.48/0.66         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.48/0.66  thf('7', plain,
% 0.48/0.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.48/0.66         (~ (r1_tarski @ X22 @ X23)
% 0.48/0.66          | (r1_xboole_0 @ X22 @ (k6_subset_1 @ X24 @ X23)))),
% 0.48/0.66      inference('demod', [status(thm)], ['5', '6'])).
% 0.48/0.66  thf('8', plain,
% 0.48/0.66      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k6_subset_1 @ X0 @ sk_B))),
% 0.48/0.66      inference('sup-', [status(thm)], ['4', '7'])).
% 0.48/0.66  thf(t83_xboole_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.48/0.66  thf('9', plain,
% 0.48/0.66      (![X19 : $i, X20 : $i]:
% 0.48/0.66         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.48/0.66      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.48/0.66  thf('10', plain,
% 0.48/0.66      (![X27 : $i, X28 : $i]:
% 0.48/0.66         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.48/0.66  thf('11', plain,
% 0.48/0.66      (![X19 : $i, X20 : $i]:
% 0.48/0.66         (((k6_subset_1 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.48/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.48/0.66  thf('12', plain,
% 0.48/0.66      (![X0 : $i]: ((k6_subset_1 @ sk_A @ (k6_subset_1 @ X0 @ sk_B)) = (sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['8', '11'])).
% 0.48/0.66  thf(d10_xboole_0, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.66  thf('13', plain,
% 0.48/0.66      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.48/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.66  thf('14', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.48/0.66      inference('simplify', [status(thm)], ['13'])).
% 0.48/0.66  thf('15', plain,
% 0.48/0.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.48/0.66         (~ (r1_tarski @ X22 @ X23)
% 0.48/0.66          | (r1_xboole_0 @ X22 @ (k6_subset_1 @ X24 @ X23)))),
% 0.48/0.66      inference('demod', [status(thm)], ['5', '6'])).
% 0.48/0.66  thf('16', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.48/0.66  thf('17', plain,
% 0.48/0.66      (![X0 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X0 @ sk_B) @ sk_A)),
% 0.48/0.66      inference('sup+', [status(thm)], ['12', '16'])).
% 0.48/0.66  thf(t207_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ C ) =>
% 0.48/0.66       ( ( r1_xboole_0 @ A @ B ) =>
% 0.48/0.66         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.48/0.66  thf('18', plain,
% 0.48/0.66      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.48/0.66         (~ (r1_xboole_0 @ X34 @ X35)
% 0.48/0.66          | ~ (v1_relat_1 @ X36)
% 0.48/0.66          | ((k7_relat_1 @ (k7_relat_1 @ X36 @ X34) @ X35) = (k1_xboole_0)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.48/0.66  thf('19', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k7_relat_1 @ (k7_relat_1 @ X1 @ (k6_subset_1 @ X0 @ sk_B)) @ sk_A)
% 0.48/0.66            = (k1_xboole_0))
% 0.48/0.66          | ~ (v1_relat_1 @ X1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.48/0.66  thf('20', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.48/0.66            = (k1_xboole_0))
% 0.48/0.66          | ~ (v1_relat_1 @ X0)
% 0.48/0.66          | ~ (v1_relat_1 @ X0))),
% 0.48/0.66      inference('sup+', [status(thm)], ['3', '19'])).
% 0.48/0.66  thf('21', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X0)
% 0.48/0.66          | ((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.48/0.66              = (k1_xboole_0)))),
% 0.48/0.66      inference('simplify', [status(thm)], ['20'])).
% 0.48/0.66  thf('22', plain,
% 0.48/0.66      (((k7_relat_1 @ (k6_subset_1 @ sk_C_2 @ (k7_relat_1 @ sk_C_2 @ sk_B)) @ 
% 0.48/0.66         sk_A) != (k1_xboole_0))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('23', plain,
% 0.48/0.66      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C_2))),
% 0.48/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.66  thf('24', plain, ((v1_relat_1 @ sk_C_2)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('25', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.48/0.66      inference('demod', [status(thm)], ['23', '24'])).
% 0.48/0.66  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.48/0.66  
% 0.48/0.66  % SZS output end Refutation
% 0.48/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
