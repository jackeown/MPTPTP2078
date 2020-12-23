%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h6lMp6osls

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:58 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 108 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  608 ( 929 expanded)
%              Number of equality atoms :   51 (  86 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
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

thf(t191_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ ( k6_subset_1 @ ( k1_relat_1 @ X13 ) @ X14 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t191_relat_1])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ ( k4_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k5_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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

thf('34',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h6lMp6osls
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:51:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 145 iterations in 0.226s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.69  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.45/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(d10_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.69  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.69      inference('simplify', [status(thm)], ['0'])).
% 0.45/0.69  thf(t211_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ C ) =>
% 0.45/0.69       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.45/0.69         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.45/0.69           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.45/0.69          | ((k6_subset_1 @ X15 @ (k7_relat_1 @ X15 @ X17))
% 0.45/0.69              = (k7_relat_1 @ X15 @ (k6_subset_1 @ X16 @ X17)))
% 0.45/0.69          | ~ (v1_relat_1 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.45/0.69  thf(redefinition_k6_subset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.45/0.69          | ((k4_xboole_0 @ X15 @ (k7_relat_1 @ X15 @ X17))
% 0.45/0.69              = (k7_relat_1 @ X15 @ (k4_xboole_0 @ X16 @ X17)))
% 0.45/0.69          | ~ (v1_relat_1 @ X15))),
% 0.45/0.69      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X0)
% 0.45/0.69          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.69              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['1', '5'])).
% 0.45/0.69  thf(t191_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( k1_relat_1 @
% 0.45/0.69           ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.45/0.69         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (![X13 : $i, X14 : $i]:
% 0.45/0.69         (((k1_relat_1 @ 
% 0.45/0.69            (k7_relat_1 @ X13 @ (k6_subset_1 @ (k1_relat_1 @ X13) @ X14)))
% 0.45/0.69            = (k6_subset_1 @ (k1_relat_1 @ X13) @ X14))
% 0.45/0.69          | ~ (v1_relat_1 @ X13))),
% 0.45/0.69      inference('cnf', [status(esa)], [t191_relat_1])).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      (![X13 : $i, X14 : $i]:
% 0.45/0.69         (((k1_relat_1 @ 
% 0.45/0.69            (k7_relat_1 @ X13 @ (k4_xboole_0 @ (k1_relat_1 @ X13) @ X14)))
% 0.45/0.69            = (k4_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 0.45/0.69          | ~ (v1_relat_1 @ X13))),
% 0.45/0.69      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.45/0.69            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ X1)
% 0.45/0.69          | ~ (v1_relat_1 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['6', '10'])).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X1)
% 0.45/0.69          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.45/0.69              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.69  thf(commutativity_k2_tarski, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.69  thf(t12_setfam_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i]:
% 0.45/0.69         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.45/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['13', '14'])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i]:
% 0.45/0.69         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.45/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.69  thf(t90_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.45/0.69         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      (![X20 : $i, X21 : $i]:
% 0.45/0.69         (((k1_relat_1 @ (k7_relat_1 @ X20 @ X21))
% 0.45/0.69            = (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21))
% 0.45/0.69          | ~ (v1_relat_1 @ X20))),
% 0.45/0.69      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.45/0.69  thf(t89_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( r1_tarski @
% 0.45/0.69         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X18 : $i, X19 : $i]:
% 0.45/0.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X18 @ X19)) @ 
% 0.45/0.69           (k1_relat_1 @ X18))
% 0.45/0.69          | ~ (v1_relat_1 @ X18))),
% 0.45/0.69      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ 
% 0.45/0.69           (k1_relat_1 @ X1))
% 0.45/0.69          | ~ (v1_relat_1 @ X1)
% 0.45/0.69          | ~ (v1_relat_1 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X1)
% 0.45/0.69          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ 
% 0.45/0.69             (k1_relat_1 @ X1)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['20'])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.45/0.69           (k1_relat_1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['17', '21'])).
% 0.45/0.69  thf(t28_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.69  thf('23', plain,
% 0.45/0.69      (![X5 : $i, X6 : $i]:
% 0.45/0.69         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.45/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X0)
% 0.45/0.69          | ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.45/0.69              (k1_relat_1 @ X0)) = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('25', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X0)
% 0.45/0.69          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.45/0.69              (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.45/0.69              = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))),
% 0.45/0.69      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.69  thf(t100_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (![X3 : $i, X4 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X3 @ X4)
% 0.45/0.69           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.45/0.69            (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.45/0.69            = (k5_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.45/0.69               (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.45/0.69          | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.69  thf('30', plain,
% 0.45/0.69      (![X3 : $i, X4 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X3 @ X4)
% 0.45/0.69           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.69  thf('31', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['29', '30'])).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.45/0.69            (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.45/0.69            = (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.45/0.69          | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['28', '31'])).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (![X20 : $i, X21 : $i]:
% 0.45/0.69         (((k1_relat_1 @ (k7_relat_1 @ X20 @ X21))
% 0.45/0.69            = (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21))
% 0.45/0.69          | ~ (v1_relat_1 @ X20))),
% 0.45/0.69      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.45/0.69  thf(t213_relat_1, conjecture,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( k6_subset_1 @
% 0.45/0.69           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.45/0.69         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i,B:$i]:
% 0.45/0.69        ( ( v1_relat_1 @ B ) =>
% 0.45/0.69          ( ( k6_subset_1 @
% 0.45/0.69              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.45/0.69            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.45/0.69  thf('34', plain,
% 0.45/0.69      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.45/0.69         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.45/0.69         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('35', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.45/0.69         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.45/0.69         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.45/0.69      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.45/0.69  thf('38', plain,
% 0.45/0.69      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.45/0.69          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.45/0.69          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.45/0.69        | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['33', '37'])).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.69  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.45/0.69         (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.45/0.69         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.45/0.69      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.45/0.69  thf('42', plain,
% 0.45/0.69      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.69          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.45/0.69        | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['32', '41'])).
% 0.45/0.69  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.69         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.45/0.69      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.69  thf('45', plain,
% 0.45/0.69      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.69          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.45/0.69        | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['12', '44'])).
% 0.45/0.69  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.69         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.69  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.56/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
