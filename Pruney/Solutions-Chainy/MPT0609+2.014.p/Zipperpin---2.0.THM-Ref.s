%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zKhXF9hIdU

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:00 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   57 (  77 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  504 ( 718 expanded)
%              Number of equality atoms :   43 (  63 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ( ( k6_subset_1 @ X19 @ ( k7_relat_1 @ X19 @ X21 ) )
        = ( k7_relat_1 @ X19 @ ( k6_subset_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ( ( k4_xboole_0 @ X19 @ ( k7_relat_1 @ X19 @ X21 ) )
        = ( k7_relat_1 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t191_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ ( k6_subset_1 @ ( k1_relat_1 @ X17 ) @ X18 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t191_relat_1])).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ ( k4_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ ( k4_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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

thf('18',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','31'])).

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
    inference('sup-',[status(thm)],['12','34'])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zKhXF9hIdU
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 88 iterations in 0.156s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.40/0.61  thf(d10_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.61  thf('0', plain,
% 0.40/0.61      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.61  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.40/0.61      inference('simplify', [status(thm)], ['0'])).
% 0.40/0.61  thf(t211_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ C ) =>
% 0.40/0.61       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.40/0.61         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.40/0.61           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.61         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.40/0.61          | ((k6_subset_1 @ X19 @ (k7_relat_1 @ X19 @ X21))
% 0.40/0.61              = (k7_relat_1 @ X19 @ (k6_subset_1 @ X20 @ X21)))
% 0.40/0.61          | ~ (v1_relat_1 @ X19))),
% 0.40/0.61      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.40/0.61  thf(redefinition_k6_subset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (![X13 : $i, X14 : $i]:
% 0.40/0.61         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X13 : $i, X14 : $i]:
% 0.40/0.61         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.61         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.40/0.61          | ((k4_xboole_0 @ X19 @ (k7_relat_1 @ X19 @ X21))
% 0.40/0.61              = (k7_relat_1 @ X19 @ (k4_xboole_0 @ X20 @ X21)))
% 0.40/0.61          | ~ (v1_relat_1 @ X19))),
% 0.40/0.61      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X0)
% 0.40/0.61          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.40/0.61              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['1', '5'])).
% 0.40/0.61  thf(t191_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( k1_relat_1 @
% 0.40/0.61           ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.40/0.61         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i]:
% 0.40/0.61         (((k1_relat_1 @ 
% 0.40/0.61            (k7_relat_1 @ X17 @ (k6_subset_1 @ (k1_relat_1 @ X17) @ X18)))
% 0.40/0.61            = (k6_subset_1 @ (k1_relat_1 @ X17) @ X18))
% 0.40/0.61          | ~ (v1_relat_1 @ X17))),
% 0.40/0.61      inference('cnf', [status(esa)], [t191_relat_1])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X13 : $i, X14 : $i]:
% 0.40/0.61         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (![X13 : $i, X14 : $i]:
% 0.40/0.61         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i]:
% 0.40/0.61         (((k1_relat_1 @ 
% 0.40/0.61            (k7_relat_1 @ X17 @ (k4_xboole_0 @ (k1_relat_1 @ X17) @ X18)))
% 0.40/0.61            = (k4_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 0.40/0.61          | ~ (v1_relat_1 @ X17))),
% 0.40/0.61      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.40/0.61            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.40/0.61          | ~ (v1_relat_1 @ X1)
% 0.40/0.61          | ~ (v1_relat_1 @ X1))),
% 0.40/0.61      inference('sup+', [status(thm)], ['6', '10'])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X1)
% 0.40/0.61          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.40/0.61              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['11'])).
% 0.40/0.61  thf(t90_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.40/0.61         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X22 : $i, X23 : $i]:
% 0.40/0.61         (((k1_relat_1 @ (k7_relat_1 @ X22 @ X23))
% 0.40/0.61            = (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23))
% 0.40/0.61          | ~ (v1_relat_1 @ X22))),
% 0.40/0.61      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i]:
% 0.40/0.61         (((k1_relat_1 @ 
% 0.40/0.61            (k7_relat_1 @ X17 @ (k4_xboole_0 @ (k1_relat_1 @ X17) @ X18)))
% 0.40/0.61            = (k4_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 0.40/0.61          | ~ (v1_relat_1 @ X17))),
% 0.40/0.61      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.40/0.61            (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.40/0.61            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.40/0.61          | ~ (v1_relat_1 @ X1)
% 0.40/0.61          | ~ (v1_relat_1 @ X1))),
% 0.40/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X1)
% 0.40/0.61          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.40/0.61              (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.40/0.61              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X22 : $i, X23 : $i]:
% 0.40/0.61         (((k1_relat_1 @ (k7_relat_1 @ X22 @ X23))
% 0.40/0.61            = (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23))
% 0.40/0.61          | ~ (v1_relat_1 @ X22))),
% 0.40/0.61      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.40/0.61  thf(t213_relat_1, conjecture,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( k6_subset_1 @
% 0.40/0.61           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.40/0.61         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i]:
% 0.40/0.61        ( ( v1_relat_1 @ B ) =>
% 0.40/0.61          ( ( k6_subset_1 @
% 0.40/0.61              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.40/0.61            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.40/0.61         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.40/0.61         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X13 : $i, X14 : $i]:
% 0.40/0.61         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X13 : $i, X14 : $i]:
% 0.40/0.61         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.40/0.61         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.40/0.61         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.40/0.61          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.40/0.61          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['17', '21'])).
% 0.40/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.61  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.40/0.61         (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.40/0.61         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.61  thf(t48_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (![X9 : $i, X10 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.40/0.61           = (k3_xboole_0 @ X9 @ X10))),
% 0.40/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      (![X9 : $i, X10 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.40/0.61           = (k3_xboole_0 @ X9 @ X10))),
% 0.40/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.61           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.61           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['26', '29'])).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.40/0.61         (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.40/0.61         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['25', '30'])).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.61          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['16', '31'])).
% 0.40/0.61  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.61         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.61  thf('35', plain,
% 0.40/0.61      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.61          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['12', '34'])).
% 0.40/0.61  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.61         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.40/0.61  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
