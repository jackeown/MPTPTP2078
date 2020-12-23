%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MxDD5IqpTE

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:01 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   57 (  69 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  492 ( 641 expanded)
%              Number of equality atoms :   38 (  50 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ( ( k6_subset_1 @ X34 @ ( k7_relat_1 @ X34 @ X36 ) )
        = ( k7_relat_1 @ X34 @ ( k6_subset_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ( ( k4_xboole_0 @ X34 @ ( k7_relat_1 @ X34 @ X36 ) )
        = ( k7_relat_1 @ X34 @ ( k4_xboole_0 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ X39 @ ( k1_relat_1 @ X40 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X40 @ X39 ) )
        = X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('14',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ X39 @ ( k1_relat_1 @ X40 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X40 @ X39 ) )
        = X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k5_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t213_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
        = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
          = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t213_relat_1])).

thf('23',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MxDD5IqpTE
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:54:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 107 iterations in 0.136s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.59  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.38/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(d10_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.59  thf('1', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.38/0.59      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.59  thf(t211_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ C ) =>
% 0.38/0.59       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.38/0.59         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.38/0.59           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.59         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 0.38/0.59          | ((k6_subset_1 @ X34 @ (k7_relat_1 @ X34 @ X36))
% 0.38/0.59              = (k7_relat_1 @ X34 @ (k6_subset_1 @ X35 @ X36)))
% 0.38/0.59          | ~ (v1_relat_1 @ X34))),
% 0.38/0.59      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.38/0.59  thf(redefinition_k6_subset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X30 : $i, X31 : $i]:
% 0.38/0.59         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X30 : $i, X31 : $i]:
% 0.38/0.59         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.59         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 0.38/0.59          | ((k4_xboole_0 @ X34 @ (k7_relat_1 @ X34 @ X36))
% 0.38/0.59              = (k7_relat_1 @ X34 @ (k4_xboole_0 @ X35 @ X36)))
% 0.38/0.59          | ~ (v1_relat_1 @ X34))),
% 0.38/0.59      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.38/0.59              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '5'])).
% 0.38/0.59  thf(t36_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.38/0.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.59  thf(t91_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ B ) =>
% 0.38/0.59       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.59         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (![X39 : $i, X40 : $i]:
% 0.38/0.59         (~ (r1_tarski @ X39 @ (k1_relat_1 @ X40))
% 0.38/0.59          | ((k1_relat_1 @ (k7_relat_1 @ X40 @ X39)) = (X39))
% 0.38/0.59          | ~ (v1_relat_1 @ X40))),
% 0.38/0.59      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ((k1_relat_1 @ 
% 0.38/0.59              (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.38/0.59              = (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.38/0.59            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1))),
% 0.38/0.59      inference('sup+', [status(thm)], ['6', '9'])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X1)
% 0.38/0.59          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.38/0.59              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.59  thf(t90_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ B ) =>
% 0.38/0.59       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.38/0.59         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (![X37 : $i, X38 : $i]:
% 0.38/0.59         (((k1_relat_1 @ (k7_relat_1 @ X37 @ X38))
% 0.38/0.59            = (k3_xboole_0 @ (k1_relat_1 @ X37) @ X38))
% 0.38/0.59          | ~ (v1_relat_1 @ X37))),
% 0.38/0.59      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.38/0.59  thf(t17_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.38/0.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X39 : $i, X40 : $i]:
% 0.38/0.59         (~ (r1_tarski @ X39 @ (k1_relat_1 @ X40))
% 0.38/0.59          | ((k1_relat_1 @ (k7_relat_1 @ X40 @ X39)) = (X39))
% 0.38/0.59          | ~ (v1_relat_1 @ X40))),
% 0.38/0.59      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ((k1_relat_1 @ 
% 0.38/0.59              (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.38/0.59              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.38/0.59            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.59            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1))),
% 0.38/0.59      inference('sup+', [status(thm)], ['12', '15'])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X1)
% 0.38/0.59          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.38/0.59              (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.59              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.59  thf(t100_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X4 @ X5)
% 0.38/0.59           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.38/0.59            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.59            = (k5_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.38/0.59               (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.38/0.59          | ~ (v1_relat_1 @ X1))),
% 0.38/0.59      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X4 @ X5)
% 0.38/0.59           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.38/0.59            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.59            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X1))),
% 0.38/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (![X37 : $i, X38 : $i]:
% 0.38/0.59         (((k1_relat_1 @ (k7_relat_1 @ X37 @ X38))
% 0.38/0.59            = (k3_xboole_0 @ (k1_relat_1 @ X37) @ X38))
% 0.38/0.59          | ~ (v1_relat_1 @ X37))),
% 0.38/0.59      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.38/0.59  thf(t213_relat_1, conjecture,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ B ) =>
% 0.38/0.59       ( ( k6_subset_1 @
% 0.38/0.59           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.38/0.59         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i,B:$i]:
% 0.38/0.59        ( ( v1_relat_1 @ B ) =>
% 0.38/0.59          ( ( k6_subset_1 @
% 0.38/0.59              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.38/0.59            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.38/0.59         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.38/0.59         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      (![X30 : $i, X31 : $i]:
% 0.38/0.59         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (![X30 : $i, X31 : $i]:
% 0.38/0.59         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.38/0.59         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.38/0.59         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.38/0.59      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.38/0.59  thf('27', plain,
% 0.38/0.59      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.38/0.59          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.38/0.59          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['22', '26'])).
% 0.38/0.59  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.38/0.59         (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.38/0.59         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.38/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.38/0.59          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['21', '29'])).
% 0.38/0.59  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.38/0.59         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.38/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.38/0.59          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['11', '32'])).
% 0.38/0.59  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.38/0.59         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['33', '34'])).
% 0.38/0.59  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
