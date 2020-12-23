%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tTwduuveGv

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  55 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  304 ( 374 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( ( k6_subset_1 @ X17 @ ( k7_relat_1 @ X17 @ X19 ) )
        = ( k7_relat_1 @ X17 @ ( k6_subset_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X7 @ X8 ) @ X8 ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf(t84_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ ( k6_subset_1 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X14 ) @ X15 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tTwduuveGv
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:24 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 57 iterations in 0.029s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.48  thf(t211_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ C ) =>
% 0.20/0.48       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.20/0.48         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.20/0.48           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.20/0.48          | ((k6_subset_1 @ X17 @ (k7_relat_1 @ X17 @ X19))
% 0.20/0.48              = (k7_relat_1 @ X17 @ (k6_subset_1 @ X18 @ X19)))
% 0.20/0.48          | ~ (v1_relat_1 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.48              = (k7_relat_1 @ X0 @ (k6_subset_1 @ (k1_relat_1 @ X0) @ X1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf(t79_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X8)),
% 0.20/0.48      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.48  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X7 @ X8) @ X8)),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(t216_relat_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ C ) =>
% 0.20/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.48         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.20/0.48           ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( v1_relat_1 @ C ) =>
% 0.20/0.48          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.48            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.20/0.48              ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.20/0.48  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(l32_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X3 : $i, X5 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.48  thf('9', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.48  thf('11', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf(t84_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.20/0.48          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X9 @ X10)
% 0.20/0.48          | ~ (r1_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 0.20/0.48          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t84_xboole_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X9 @ X10)
% 0.20/0.48          | ~ (r1_xboole_0 @ X9 @ (k6_subset_1 @ X10 @ X11))
% 0.20/0.48          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ sk_B)
% 0.20/0.48          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.48  thf('16', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X0 @ sk_B) @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '17'])).
% 0.20/0.48  thf(t207_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ C ) =>
% 0.20/0.48       ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.48         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ X14 @ X15)
% 0.20/0.48          | ~ (v1_relat_1 @ X16)
% 0.20/0.48          | ((k7_relat_1 @ (k7_relat_1 @ X16 @ X14) @ X15) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k7_relat_1 @ (k7_relat_1 @ X1 @ (k6_subset_1 @ X0 @ sk_B)) @ sk_A)
% 0.20/0.48            = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.20/0.48            = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['3', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.20/0.48              = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.20/0.48         != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
