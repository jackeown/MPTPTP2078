%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NOGI9hv8nK

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  73 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  506 ( 670 expanded)
%              Number of equality atoms :   38 (  52 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X41 ) @ X42 )
      | ( ( k6_subset_1 @ X41 @ ( k7_relat_1 @ X41 @ X43 ) )
        = ( k7_relat_1 @ X41 @ ( k6_subset_1 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X41 ) @ X42 )
      | ( ( k4_xboole_0 @ X41 @ ( k7_relat_1 @ X41 @ X43 ) )
        = ( k7_relat_1 @ X41 @ ( k4_xboole_0 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k4_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('10',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ X46 @ ( k1_relat_1 @ X47 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) )
        = X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X44 @ X45 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ X46 @ ( k1_relat_1 @ X47 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) )
        = X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k5_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X44 @ X45 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
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

thf('25',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NOGI9hv8nK
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 69 iterations in 0.133s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.57  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(d10_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.57  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.57      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.57  thf(t211_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ C ) =>
% 0.20/0.57       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.20/0.57         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.20/0.57           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.57         (~ (r1_tarski @ (k1_relat_1 @ X41) @ X42)
% 0.20/0.57          | ((k6_subset_1 @ X41 @ (k7_relat_1 @ X41 @ X43))
% 0.20/0.57              = (k7_relat_1 @ X41 @ (k6_subset_1 @ X42 @ X43)))
% 0.20/0.57          | ~ (v1_relat_1 @ X41))),
% 0.20/0.57      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.20/0.57  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X37 : $i, X38 : $i]:
% 0.20/0.57         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X37 : $i, X38 : $i]:
% 0.20/0.57         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.57         (~ (r1_tarski @ (k1_relat_1 @ X41) @ X42)
% 0.20/0.57          | ((k4_xboole_0 @ X41 @ (k7_relat_1 @ X41 @ X43))
% 0.20/0.57              = (k7_relat_1 @ X41 @ (k4_xboole_0 @ X42 @ X43)))
% 0.20/0.57          | ~ (v1_relat_1 @ X41))),
% 0.20/0.57      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X0)
% 0.20/0.57          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.57              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.57  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.57      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.57  thf(t109_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k4_xboole_0 @ X5 @ X7) @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf(t91_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ B ) =>
% 0.20/0.57       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.57         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X46 : $i, X47 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X46 @ (k1_relat_1 @ X47))
% 0.20/0.57          | ((k1_relat_1 @ (k7_relat_1 @ X47 @ X46)) = (X46))
% 0.20/0.57          | ~ (v1_relat_1 @ X47))),
% 0.20/0.57      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X0)
% 0.20/0.57          | ((k1_relat_1 @ 
% 0.20/0.57              (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.20/0.57              = (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.57            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ X1)
% 0.20/0.57          | ~ (v1_relat_1 @ X1))),
% 0.20/0.57      inference('sup+', [status(thm)], ['6', '11'])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X1)
% 0.20/0.57          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.57              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.57  thf(t90_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ B ) =>
% 0.20/0.57       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.20/0.57         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X44 : $i, X45 : $i]:
% 0.20/0.57         (((k1_relat_1 @ (k7_relat_1 @ X44 @ X45))
% 0.20/0.57            = (k3_xboole_0 @ (k1_relat_1 @ X44) @ X45))
% 0.20/0.57          | ~ (v1_relat_1 @ X44))),
% 0.20/0.57      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.20/0.57  thf(t17_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.20/0.57      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X46 : $i, X47 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X46 @ (k1_relat_1 @ X47))
% 0.20/0.57          | ((k1_relat_1 @ (k7_relat_1 @ X47 @ X46)) = (X46))
% 0.20/0.57          | ~ (v1_relat_1 @ X47))),
% 0.20/0.57      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X0)
% 0.20/0.57          | ((k1_relat_1 @ 
% 0.20/0.57              (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.20/0.57              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.20/0.57            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.57            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ X1)
% 0.20/0.57          | ~ (v1_relat_1 @ X1))),
% 0.20/0.57      inference('sup+', [status(thm)], ['14', '17'])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X1)
% 0.20/0.57          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.20/0.57              (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.57              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.57  thf(t100_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X3 : $i, X4 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X3 @ X4)
% 0.20/0.57           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.20/0.57            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.57            = (k5_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.20/0.57               (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.20/0.57          | ~ (v1_relat_1 @ X1))),
% 0.20/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X3 : $i, X4 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X3 @ X4)
% 0.20/0.57           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.20/0.57            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.57            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ X1))),
% 0.20/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (![X44 : $i, X45 : $i]:
% 0.20/0.57         (((k1_relat_1 @ (k7_relat_1 @ X44 @ X45))
% 0.20/0.57            = (k3_xboole_0 @ (k1_relat_1 @ X44) @ X45))
% 0.20/0.57          | ~ (v1_relat_1 @ X44))),
% 0.20/0.57      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.20/0.57  thf(t213_relat_1, conjecture,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ B ) =>
% 0.20/0.57       ( ( k6_subset_1 @
% 0.20/0.57           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.20/0.57         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i,B:$i]:
% 0.20/0.57        ( ( v1_relat_1 @ B ) =>
% 0.20/0.57          ( ( k6_subset_1 @
% 0.20/0.57              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.20/0.57            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.20/0.57         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.20/0.57         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (![X37 : $i, X38 : $i]:
% 0.20/0.57         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (![X37 : $i, X38 : $i]:
% 0.20/0.57         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.20/0.57         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.20/0.57         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.20/0.57          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.57          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.20/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['24', '28'])).
% 0.20/0.57  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.20/0.57         (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.57         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.57          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.20/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['23', '31'])).
% 0.20/0.57  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.57         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.57          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['13', '34'])).
% 0.20/0.57  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.57         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.57  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
