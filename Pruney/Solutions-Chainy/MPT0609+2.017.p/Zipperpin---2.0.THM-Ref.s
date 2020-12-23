%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TFQXElubh3

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:01 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   72 (  90 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  587 ( 760 expanded)
%              Number of equality atoms :   54 (  71 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( ( k6_subset_1 @ X15 @ ( k7_relat_1 @ X15 @ X17 ) )
        = ( k7_relat_1 @ X15 @ ( k6_subset_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( ( k4_xboole_0 @ X15 @ ( k7_relat_1 @ X15 @ X17 ) )
        = ( k7_relat_1 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','45'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TFQXElubh3
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.77  % Solved by: fo/fo7.sh
% 0.53/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.77  % done 391 iterations in 0.307s
% 0.53/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.77  % SZS output start Refutation
% 0.53/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.53/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.77  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.53/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.77  thf(d10_xboole_0, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.77  thf('0', plain,
% 0.53/0.77      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.53/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.77  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.53/0.77      inference('simplify', [status(thm)], ['0'])).
% 0.53/0.77  thf(t211_relat_1, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( v1_relat_1 @ C ) =>
% 0.53/0.77       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.53/0.77         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.53/0.77           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.53/0.77  thf('2', plain,
% 0.53/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.53/0.77         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.53/0.77          | ((k6_subset_1 @ X15 @ (k7_relat_1 @ X15 @ X17))
% 0.53/0.77              = (k7_relat_1 @ X15 @ (k6_subset_1 @ X16 @ X17)))
% 0.53/0.77          | ~ (v1_relat_1 @ X15))),
% 0.53/0.77      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.53/0.77  thf(redefinition_k6_subset_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.53/0.77  thf('3', plain,
% 0.53/0.77      (![X13 : $i, X14 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('4', plain,
% 0.53/0.77      (![X13 : $i, X14 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('5', plain,
% 0.53/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.53/0.77         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.53/0.77          | ((k4_xboole_0 @ X15 @ (k7_relat_1 @ X15 @ X17))
% 0.53/0.77              = (k7_relat_1 @ X15 @ (k4_xboole_0 @ X16 @ X17)))
% 0.53/0.77          | ~ (v1_relat_1 @ X15))),
% 0.53/0.77      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.53/0.77  thf('6', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (v1_relat_1 @ X0)
% 0.53/0.77          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.53/0.77              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['1', '5'])).
% 0.53/0.77  thf(t90_relat_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( v1_relat_1 @ B ) =>
% 0.53/0.77       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.53/0.77         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.53/0.77  thf('7', plain,
% 0.53/0.77      (![X18 : $i, X19 : $i]:
% 0.53/0.77         (((k1_relat_1 @ (k7_relat_1 @ X18 @ X19))
% 0.53/0.77            = (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 0.53/0.77          | ~ (v1_relat_1 @ X18))),
% 0.53/0.77      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.53/0.77  thf('8', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.53/0.77            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.53/0.77               (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.53/0.77          | ~ (v1_relat_1 @ X1)
% 0.53/0.77          | ~ (v1_relat_1 @ X1))),
% 0.53/0.77      inference('sup+', [status(thm)], ['6', '7'])).
% 0.53/0.77  thf('9', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (v1_relat_1 @ X1)
% 0.53/0.77          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.53/0.77              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.53/0.77                 (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 0.53/0.77      inference('simplify', [status(thm)], ['8'])).
% 0.53/0.77  thf(t17_xboole_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.77  thf('10', plain,
% 0.53/0.77      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.53/0.77      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.77  thf(t28_xboole_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.77  thf('11', plain,
% 0.53/0.77      (![X9 : $i, X10 : $i]:
% 0.53/0.77         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.53/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.77  thf('12', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.53/0.77           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.53/0.77  thf(commutativity_k3_xboole_0, axiom,
% 0.53/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.53/0.77  thf('13', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.77  thf('14', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.53/0.77           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.77      inference('demod', [status(thm)], ['12', '13'])).
% 0.53/0.77  thf(t100_xboole_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.77  thf('15', plain,
% 0.53/0.77      (![X5 : $i, X6 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.77           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.77  thf('16', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.77           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.77      inference('sup+', [status(thm)], ['14', '15'])).
% 0.53/0.77  thf('17', plain,
% 0.53/0.77      (![X5 : $i, X6 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.77           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.77  thf('18', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.77           = (k4_xboole_0 @ X1 @ X0))),
% 0.53/0.77      inference('demod', [status(thm)], ['16', '17'])).
% 0.53/0.77  thf(t48_xboole_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.77  thf('19', plain,
% 0.53/0.77      (![X11 : $i, X12 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.53/0.77           = (k3_xboole_0 @ X11 @ X12))),
% 0.53/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.77  thf('20', plain,
% 0.53/0.77      (![X11 : $i, X12 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.53/0.77           = (k3_xboole_0 @ X11 @ X12))),
% 0.53/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.77  thf('21', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.77           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.77      inference('sup+', [status(thm)], ['19', '20'])).
% 0.53/0.77  thf('22', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X1 @ X0)
% 0.53/0.77           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.77      inference('sup+', [status(thm)], ['18', '21'])).
% 0.53/0.77  thf('23', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (v1_relat_1 @ X1)
% 0.53/0.77          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.53/0.77              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.53/0.77      inference('demod', [status(thm)], ['9', '22'])).
% 0.53/0.77  thf('24', plain,
% 0.53/0.77      (![X18 : $i, X19 : $i]:
% 0.53/0.77         (((k1_relat_1 @ (k7_relat_1 @ X18 @ X19))
% 0.53/0.77            = (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 0.53/0.77          | ~ (v1_relat_1 @ X18))),
% 0.53/0.77      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.53/0.77  thf(t213_relat_1, conjecture,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( v1_relat_1 @ B ) =>
% 0.53/0.77       ( ( k6_subset_1 @
% 0.53/0.77           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.53/0.77         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.53/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.77    (~( ![A:$i,B:$i]:
% 0.53/0.77        ( ( v1_relat_1 @ B ) =>
% 0.53/0.77          ( ( k6_subset_1 @
% 0.53/0.77              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.53/0.77            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.53/0.77    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.53/0.77  thf('25', plain,
% 0.53/0.77      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.53/0.77         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.53/0.77         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('26', plain,
% 0.53/0.77      (![X13 : $i, X14 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('27', plain,
% 0.53/0.77      (![X13 : $i, X14 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('28', plain,
% 0.53/0.77      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.53/0.77         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.53/0.77         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.53/0.77      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.53/0.77  thf('29', plain,
% 0.53/0.77      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.53/0.77          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.53/0.77          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.53/0.77        | ~ (v1_relat_1 @ sk_B))),
% 0.53/0.77      inference('sup-', [status(thm)], ['24', '28'])).
% 0.53/0.77  thf('30', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.77  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('32', plain,
% 0.53/0.77      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.53/0.77         (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.77         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.53/0.77      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.53/0.77  thf('33', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.77  thf('34', plain,
% 0.53/0.77      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.53/0.77      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.77  thf('35', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.53/0.77      inference('sup+', [status(thm)], ['33', '34'])).
% 0.53/0.77  thf('36', plain,
% 0.53/0.77      (![X9 : $i, X10 : $i]:
% 0.53/0.77         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.53/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.77  thf('37', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.53/0.77           = (k3_xboole_0 @ X1 @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['35', '36'])).
% 0.53/0.77  thf('38', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.77  thf('39', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.77           = (k3_xboole_0 @ X1 @ X0))),
% 0.53/0.77      inference('demod', [status(thm)], ['37', '38'])).
% 0.53/0.77  thf('40', plain,
% 0.53/0.77      (![X5 : $i, X6 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.77           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.77  thf('41', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.77           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.77      inference('sup+', [status(thm)], ['39', '40'])).
% 0.53/0.77  thf('42', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.77  thf('43', plain,
% 0.53/0.77      (![X5 : $i, X6 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.77           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.77  thf('44', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.53/0.77           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.77      inference('sup+', [status(thm)], ['42', '43'])).
% 0.53/0.77  thf('45', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.77           = (k4_xboole_0 @ X0 @ X1))),
% 0.53/0.77      inference('demod', [status(thm)], ['41', '44'])).
% 0.53/0.77  thf('46', plain,
% 0.53/0.77      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.53/0.77         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.53/0.77      inference('demod', [status(thm)], ['32', '45'])).
% 0.53/0.77  thf('47', plain,
% 0.53/0.77      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.53/0.77          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.53/0.77        | ~ (v1_relat_1 @ sk_B))),
% 0.53/0.77      inference('sup-', [status(thm)], ['23', '46'])).
% 0.53/0.77  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('49', plain,
% 0.53/0.77      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.53/0.77         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.53/0.77      inference('demod', [status(thm)], ['47', '48'])).
% 0.53/0.77  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 0.53/0.77  
% 0.53/0.77  % SZS output end Refutation
% 0.53/0.77  
% 0.61/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
