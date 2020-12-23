%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2zaM8I6frZ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:12 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  339 ( 417 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k6_subset_1 @ X12 @ ( k7_relat_1 @ X12 @ X14 ) )
        = ( k7_relat_1 @ X12 @ ( k6_subset_1 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k4_xboole_0 @ X12 @ ( k7_relat_1 @ X12 @ X14 ) )
        = ( k7_relat_1 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X2 ) )
        = ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

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

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_xboole_0 @ X5 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_xboole_0 @ X5 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) @ sk_A )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( ( k7_relat_1 @ X17 @ X18 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','23'])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2zaM8I6frZ
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:30:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 178 iterations in 0.115s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.39/0.57  thf(t7_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.39/0.57  thf(t211_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ C ) =>
% 0.39/0.57       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.39/0.57         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.39/0.57           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.39/0.57          | ((k6_subset_1 @ X12 @ (k7_relat_1 @ X12 @ X14))
% 0.39/0.57              = (k7_relat_1 @ X12 @ (k6_subset_1 @ X13 @ X14)))
% 0.39/0.57          | ~ (v1_relat_1 @ X12))),
% 0.39/0.57      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.39/0.57  thf(redefinition_k6_subset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.39/0.57          | ((k4_xboole_0 @ X12 @ (k7_relat_1 @ X12 @ X14))
% 0.39/0.57              = (k7_relat_1 @ X12 @ (k4_xboole_0 @ X13 @ X14)))
% 0.39/0.57          | ~ (v1_relat_1 @ X12))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X1)
% 0.39/0.57          | ((k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X2))
% 0.39/0.57              = (k7_relat_1 @ X1 @ 
% 0.39/0.57                 (k4_xboole_0 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '4'])).
% 0.39/0.57  thf(t216_relat_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ C ) =>
% 0.39/0.57       ( ( r1_tarski @ A @ B ) =>
% 0.39/0.57         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.39/0.57           ( k1_xboole_0 ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.57        ( ( v1_relat_1 @ C ) =>
% 0.39/0.57          ( ( r1_tarski @ A @ B ) =>
% 0.39/0.57            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.39/0.57              ( k1_xboole_0 ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.39/0.57  thf('6', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t85_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X5 @ X6)
% 0.39/0.57          | (r1_xboole_0 @ X5 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf(t83_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i]:
% 0.39/0.57         (((k4_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)) = (sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf(t87_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X15 : $i, X16 : $i]:
% 0.39/0.57         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X15 @ X16)) @ X16)
% 0.39/0.57          | ~ (v1_relat_1 @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X5 @ X6)
% 0.39/0.57          | (r1_xboole_0 @ X5 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X1)
% 0.39/0.57          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.39/0.57             (k4_xboole_0 @ X2 @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ 
% 0.39/0.57           (k1_relat_1 @ (k7_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_B))) @ sk_A)
% 0.39/0.57          | ~ (v1_relat_1 @ X1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['10', '13'])).
% 0.39/0.57  thf(t95_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.57         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i]:
% 0.39/0.57         (~ (r1_xboole_0 @ (k1_relat_1 @ X17) @ X18)
% 0.39/0.57          | ((k7_relat_1 @ X17 @ X18) = (k1_xboole_0))
% 0.39/0.57          | ~ (v1_relat_1 @ X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X1)
% 0.39/0.57          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.39/0.57          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_B)) @ sk_A)
% 0.39/0.57              = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf(dt_k7_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((k7_relat_1 @ (k7_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_B)) @ sk_A)
% 0.39/0.58            = (k1_xboole_0))
% 0.39/0.58          | ~ (v1_relat_1 @ X1))),
% 0.39/0.58      inference('clc', [status(thm)], ['16', '17'])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.39/0.58            = (k1_xboole_0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['5', '18'])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.39/0.58              = (k1_xboole_0)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.39/0.58         != (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (((k7_relat_1 @ (k4_xboole_0 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.39/0.58         != (k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['20', '23'])).
% 0.39/0.58  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('26', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
