%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lyn62a6CoN

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:59 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 116 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  644 (1061 expanded)
%              Number of equality atoms :   58 ( 101 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X16 @ ( k7_relat_1 @ X16 @ X17 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X16 @ ( k7_relat_1 @ X16 @ X17 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
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

thf('5',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','44'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lyn62a6CoN
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:24:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.59  % Solved by: fo/fo7.sh
% 0.35/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.59  % done 145 iterations in 0.125s
% 0.35/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.59  % SZS output start Refutation
% 0.35/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.59  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.35/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.35/0.59  thf(t212_relat_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( v1_relat_1 @ B ) =>
% 0.35/0.59       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.35/0.59         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.59  thf('0', plain,
% 0.35/0.59      (![X16 : $i, X17 : $i]:
% 0.35/0.59         (((k1_relat_1 @ (k6_subset_1 @ X16 @ (k7_relat_1 @ X16 @ X17)))
% 0.35/0.59            = (k6_subset_1 @ (k1_relat_1 @ X16) @ X17))
% 0.35/0.59          | ~ (v1_relat_1 @ X16))),
% 0.35/0.59      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.35/0.59  thf(redefinition_k6_subset_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.35/0.59  thf('1', plain,
% 0.35/0.59      (![X12 : $i, X13 : $i]:
% 0.35/0.59         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.35/0.59  thf('2', plain,
% 0.35/0.59      (![X12 : $i, X13 : $i]:
% 0.35/0.59         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.35/0.59  thf('3', plain,
% 0.35/0.59      (![X16 : $i, X17 : $i]:
% 0.35/0.59         (((k1_relat_1 @ (k4_xboole_0 @ X16 @ (k7_relat_1 @ X16 @ X17)))
% 0.35/0.59            = (k4_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 0.35/0.59          | ~ (v1_relat_1 @ X16))),
% 0.35/0.59      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.35/0.59  thf(t90_relat_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( v1_relat_1 @ B ) =>
% 0.35/0.59       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.35/0.59         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.59  thf('4', plain,
% 0.35/0.59      (![X18 : $i, X19 : $i]:
% 0.35/0.59         (((k1_relat_1 @ (k7_relat_1 @ X18 @ X19))
% 0.35/0.59            = (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 0.35/0.59          | ~ (v1_relat_1 @ X18))),
% 0.35/0.59      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.35/0.59  thf(t213_relat_1, conjecture,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( v1_relat_1 @ B ) =>
% 0.35/0.59       ( ( k6_subset_1 @
% 0.35/0.59           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.35/0.59         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.35/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.59    (~( ![A:$i,B:$i]:
% 0.35/0.59        ( ( v1_relat_1 @ B ) =>
% 0.35/0.59          ( ( k6_subset_1 @
% 0.35/0.59              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.35/0.59            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.35/0.59    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.35/0.59  thf('5', plain,
% 0.35/0.59      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.35/0.59         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.35/0.59         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('6', plain,
% 0.35/0.59      (![X12 : $i, X13 : $i]:
% 0.35/0.59         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.35/0.59  thf('7', plain,
% 0.35/0.59      (![X12 : $i, X13 : $i]:
% 0.35/0.59         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.35/0.59  thf('8', plain,
% 0.35/0.59      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.35/0.59         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.35/0.59         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.35/0.59      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.35/0.59  thf('9', plain,
% 0.35/0.59      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.35/0.59          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.35/0.59          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.35/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.59      inference('sup-', [status(thm)], ['4', '8'])).
% 0.35/0.59  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('11', plain,
% 0.35/0.59      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.35/0.59         (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.35/0.59         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.35/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.35/0.59  thf(commutativity_k2_tarski, axiom,
% 0.35/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.35/0.59  thf('12', plain,
% 0.35/0.59      (![X10 : $i, X11 : $i]:
% 0.35/0.59         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.35/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.59  thf(t12_setfam_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.59  thf('13', plain,
% 0.35/0.59      (![X14 : $i, X15 : $i]:
% 0.35/0.59         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.35/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.35/0.59  thf('14', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.35/0.59  thf('15', plain,
% 0.35/0.59      (![X14 : $i, X15 : $i]:
% 0.35/0.59         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.35/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.35/0.59  thf('16', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.35/0.59  thf('17', plain,
% 0.35/0.59      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.35/0.59         (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.35/0.59         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.35/0.59      inference('demod', [status(thm)], ['11', '16'])).
% 0.35/0.59  thf('18', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.35/0.59  thf(t48_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.59  thf('19', plain,
% 0.35/0.59      (![X8 : $i, X9 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.35/0.59           = (k3_xboole_0 @ X8 @ X9))),
% 0.35/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.35/0.59  thf('20', plain,
% 0.35/0.59      (![X8 : $i, X9 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.35/0.59           = (k3_xboole_0 @ X8 @ X9))),
% 0.35/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.35/0.59  thf('21', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.35/0.59           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('sup+', [status(thm)], ['19', '20'])).
% 0.35/0.59  thf('22', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.35/0.59           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.35/0.59      inference('sup+', [status(thm)], ['18', '21'])).
% 0.35/0.59  thf('23', plain,
% 0.35/0.59      (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.35/0.59         (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.35/0.59         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.35/0.59      inference('demod', [status(thm)], ['17', '22'])).
% 0.35/0.59  thf(d4_xboole_0, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i]:
% 0.35/0.59     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.35/0.59       ( ![D:$i]:
% 0.35/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.59           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.35/0.59  thf('24', plain,
% 0.35/0.59      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.35/0.59         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.35/0.59          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.35/0.59          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.35/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.35/0.59  thf('25', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.59          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('eq_fact', [status(thm)], ['24'])).
% 0.35/0.59  thf('26', plain,
% 0.35/0.59      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.59         (~ (r2_hidden @ X4 @ X3)
% 0.35/0.59          | (r2_hidden @ X4 @ X2)
% 0.35/0.59          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.35/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.35/0.59  thf('27', plain,
% 0.35/0.59      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.35/0.59         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.35/0.59      inference('simplify', [status(thm)], ['26'])).
% 0.35/0.59  thf('28', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.59         (((k3_xboole_0 @ X1 @ X0)
% 0.35/0.59            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.35/0.59          | (r2_hidden @ 
% 0.35/0.59             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 0.35/0.59             X0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['25', '27'])).
% 0.35/0.59  thf('29', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.59          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('eq_fact', [status(thm)], ['24'])).
% 0.35/0.59  thf('30', plain,
% 0.35/0.59      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.35/0.59         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.35/0.59          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.35/0.59          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.35/0.59          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.35/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.35/0.59  thf('31', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.35/0.59          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.59          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.35/0.59          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.59  thf('32', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.35/0.59          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.59          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('simplify', [status(thm)], ['31'])).
% 0.35/0.59  thf('33', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.59          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('eq_fact', [status(thm)], ['24'])).
% 0.35/0.59  thf('34', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.35/0.59          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.35/0.59      inference('clc', [status(thm)], ['32', '33'])).
% 0.35/0.59  thf('35', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (((k3_xboole_0 @ X1 @ X0)
% 0.35/0.59            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.35/0.59          | ((k3_xboole_0 @ X1 @ X0)
% 0.35/0.59              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.35/0.59      inference('sup-', [status(thm)], ['28', '34'])).
% 0.35/0.59  thf('36', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k3_xboole_0 @ X1 @ X0)
% 0.35/0.59           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('simplify', [status(thm)], ['35'])).
% 0.35/0.59  thf(t100_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.59  thf('37', plain,
% 0.35/0.59      (![X6 : $i, X7 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X6 @ X7)
% 0.35/0.59           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.59  thf('38', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.35/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('sup+', [status(thm)], ['36', '37'])).
% 0.35/0.59  thf('39', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.35/0.59  thf('40', plain,
% 0.35/0.59      (![X6 : $i, X7 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X6 @ X7)
% 0.35/0.59           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.59  thf('41', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.35/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('sup+', [status(thm)], ['39', '40'])).
% 0.35/0.59  thf('42', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.35/0.59           = (k4_xboole_0 @ X0 @ X1))),
% 0.35/0.59      inference('demod', [status(thm)], ['38', '41'])).
% 0.35/0.59  thf('43', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.35/0.59           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.35/0.59      inference('sup+', [status(thm)], ['18', '21'])).
% 0.35/0.59  thf('44', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X1 @ X0)
% 0.35/0.59           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.35/0.59  thf('45', plain,
% 0.35/0.59      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.35/0.59         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.35/0.59      inference('demod', [status(thm)], ['23', '44'])).
% 0.35/0.59  thf('46', plain,
% 0.35/0.59      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.35/0.59          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.35/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.59      inference('sup-', [status(thm)], ['3', '45'])).
% 0.35/0.59  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('48', plain,
% 0.35/0.59      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.35/0.59         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.35/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.59  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 0.35/0.59  
% 0.35/0.59  % SZS output end Refutation
% 0.35/0.59  
% 0.35/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
