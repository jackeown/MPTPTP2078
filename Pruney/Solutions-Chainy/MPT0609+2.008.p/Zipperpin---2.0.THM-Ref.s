%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WlZyVwpnIe

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:59 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   64 (  91 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  524 ( 788 expanded)
%              Number of equality atoms :   43 (  70 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X10 @ ( k7_relat_1 @ X10 @ X11 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X10 @ ( k7_relat_1 @ X10 @ X11 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k5_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf('27',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WlZyVwpnIe
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 196 iterations in 0.170s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.60  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.37/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.60  thf(t212_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ B ) =>
% 0.37/0.60       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.37/0.60         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      (![X10 : $i, X11 : $i]:
% 0.37/0.60         (((k1_relat_1 @ (k6_subset_1 @ X10 @ (k7_relat_1 @ X10 @ X11)))
% 0.37/0.60            = (k6_subset_1 @ (k1_relat_1 @ X10) @ X11))
% 0.37/0.60          | ~ (v1_relat_1 @ X10))),
% 0.37/0.60      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.37/0.60  thf(redefinition_k6_subset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.60  thf('2', plain,
% 0.37/0.60      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      (![X10 : $i, X11 : $i]:
% 0.37/0.60         (((k1_relat_1 @ (k4_xboole_0 @ X10 @ (k7_relat_1 @ X10 @ X11)))
% 0.37/0.60            = (k4_xboole_0 @ (k1_relat_1 @ X10) @ X11))
% 0.37/0.60          | ~ (v1_relat_1 @ X10))),
% 0.37/0.60      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.37/0.60  thf(t90_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ B ) =>
% 0.37/0.60       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.37/0.60         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.37/0.60  thf('4', plain,
% 0.37/0.60      (![X14 : $i, X15 : $i]:
% 0.37/0.60         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.37/0.60            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.37/0.60          | ~ (v1_relat_1 @ X14))),
% 0.37/0.60      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.37/0.60  thf(commutativity_k2_tarski, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.60  thf(t12_setfam_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (![X8 : $i, X9 : $i]:
% 0.37/0.60         ((k1_setfam_1 @ (k2_tarski @ X8 @ X9)) = (k3_xboole_0 @ X8 @ X9))),
% 0.37/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.60  thf('8', plain,
% 0.37/0.60      (![X8 : $i, X9 : $i]:
% 0.37/0.60         ((k1_setfam_1 @ (k2_tarski @ X8 @ X9)) = (k3_xboole_0 @ X8 @ X9))),
% 0.37/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (![X14 : $i, X15 : $i]:
% 0.37/0.60         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.37/0.60            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.37/0.60          | ~ (v1_relat_1 @ X14))),
% 0.37/0.60      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.37/0.60  thf(t89_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ B ) =>
% 0.37/0.60       ( r1_tarski @
% 0.37/0.60         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.37/0.60  thf('11', plain,
% 0.37/0.60      (![X12 : $i, X13 : $i]:
% 0.37/0.60         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X12 @ X13)) @ 
% 0.37/0.60           (k1_relat_1 @ X12))
% 0.37/0.60          | ~ (v1_relat_1 @ X12))),
% 0.37/0.60      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ 
% 0.37/0.60           (k1_relat_1 @ X1))
% 0.37/0.60          | ~ (v1_relat_1 @ X1)
% 0.37/0.60          | ~ (v1_relat_1 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.60  thf('13', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (v1_relat_1 @ X1)
% 0.37/0.60          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ 
% 0.37/0.60             (k1_relat_1 @ X1)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.60  thf('14', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.37/0.60           (k1_relat_1 @ X0))
% 0.37/0.60          | ~ (v1_relat_1 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['9', '13'])).
% 0.37/0.60  thf(t91_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ B ) =>
% 0.37/0.60       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.60         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (![X16 : $i, X17 : $i]:
% 0.37/0.60         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.37/0.60          | ((k1_relat_1 @ (k7_relat_1 @ X17 @ X16)) = (X16))
% 0.37/0.60          | ~ (v1_relat_1 @ X17))),
% 0.37/0.60      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (v1_relat_1 @ X0)
% 0.37/0.60          | ~ (v1_relat_1 @ X0)
% 0.37/0.60          | ((k1_relat_1 @ 
% 0.37/0.60              (k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.37/0.60              = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k1_relat_1 @ 
% 0.37/0.60            (k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.37/0.60            = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.37/0.60          | ~ (v1_relat_1 @ X0))),
% 0.37/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.37/0.60            (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.37/0.60            = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.37/0.60          | ~ (v1_relat_1 @ X0)
% 0.37/0.60          | ~ (v1_relat_1 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['4', '17'])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (v1_relat_1 @ X0)
% 0.37/0.60          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.37/0.60              (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.37/0.60              = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))),
% 0.37/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.60  thf(t100_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.37/0.60            (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.37/0.60            = (k5_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.37/0.60               (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.37/0.60          | ~ (v1_relat_1 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.60  thf('24', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.60  thf('25', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.37/0.60            (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.37/0.60            = (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.37/0.60          | ~ (v1_relat_1 @ X0))),
% 0.37/0.60      inference('demod', [status(thm)], ['21', '24'])).
% 0.37/0.60  thf('26', plain,
% 0.37/0.60      (![X14 : $i, X15 : $i]:
% 0.37/0.60         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.37/0.60            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.37/0.60          | ~ (v1_relat_1 @ X14))),
% 0.37/0.60      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.37/0.60  thf(t213_relat_1, conjecture,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ B ) =>
% 0.37/0.60       ( ( k6_subset_1 @
% 0.37/0.60           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.37/0.60         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i,B:$i]:
% 0.37/0.60        ( ( v1_relat_1 @ B ) =>
% 0.37/0.60          ( ( k6_subset_1 @
% 0.37/0.60              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.37/0.60            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.37/0.60         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.37/0.60         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('28', plain,
% 0.37/0.60      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.37/0.60         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.37/0.60         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.37/0.60      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.37/0.60          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.37/0.60          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.37/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['26', '30'])).
% 0.37/0.60  thf('32', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.60  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.37/0.60         (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.37/0.60         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.37/0.60      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.37/0.60          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.37/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['25', '34'])).
% 0.37/0.60  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('37', plain,
% 0.37/0.60      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.37/0.60         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.37/0.60      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.37/0.60          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.37/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['3', '37'])).
% 0.37/0.60  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('40', plain,
% 0.37/0.60      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.37/0.60         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.37/0.60      inference('demod', [status(thm)], ['38', '39'])).
% 0.37/0.60  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
