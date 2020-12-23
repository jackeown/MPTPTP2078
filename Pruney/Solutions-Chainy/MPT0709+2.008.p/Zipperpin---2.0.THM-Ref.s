%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RqjsLCQxTJ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:06 EST 2020

% Result     : Theorem 4.67s
% Output     : Refutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :  250 (1379 expanded)
%              Number of leaves         :   36 ( 455 expanded)
%              Depth                    :   49
%              Number of atoms          : 2146 (12611 expanded)
%              Number of equality atoms :  124 (1014 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X38 @ ( k1_relat_1 @ X39 ) )
      | ( r1_tarski @ X38 @ ( k10_relat_1 @ X39 @ ( k9_relat_1 @ X39 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X27: $i] :
      ( ( ( k9_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X38 @ ( k1_relat_1 @ X39 ) )
      | ( r1_tarski @ X38 @ ( k10_relat_1 @ X39 @ ( k9_relat_1 @ X39 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('31',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k6_subset_1 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k6_subset_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k6_subset_1 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k6_subset_1 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('44',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('49',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ X0 )
      = ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('56',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('60',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('61',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('62',plain,(
    ! [X20: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,(
    ! [X27: $i] :
      ( ( ( k9_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('71',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k9_relat_1 @ X43 @ ( k10_relat_1 @ X43 @ X42 ) )
        = ( k3_xboole_0 @ X42 @ ( k9_relat_1 @ X43 @ ( k1_relat_1 @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','65'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('75',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k10_relat_1 @ X35 @ ( k6_subset_1 @ X36 @ X37 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X35 @ X36 ) @ ( k10_relat_1 @ X35 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('78',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('79',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('80',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ X40 @ ( k2_relat_1 @ X41 ) )
      | ( ( k9_relat_1 @ X41 @ ( k10_relat_1 @ X41 @ X40 ) )
        = X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k6_subset_1 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('85',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('86',plain,(
    ! [X27: $i] :
      ( ( ( k9_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('87',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('88',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('89',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k6_subset_1 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('91',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','93'])).

thf('95',plain,(
    ! [X20: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k6_subset_1 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('98',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['92'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k6_subset_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('105',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('106',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k6_subset_1 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k1_xboole_0
      = ( k6_subset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k6_subset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k6_subset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['92'])).

thf('110',plain,
    ( k1_xboole_0
    = ( k6_subset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('112',plain,
    ( ( k6_subset_1 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('114',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('116',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('117',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['114','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('122',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('123',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_subset_1 @ ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['120','125'])).

thf('127',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('128',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_subset_1 @ ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k6_subset_1 @ ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','128'])).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('130',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k9_relat_1 @ X32 @ ( k6_subset_1 @ X33 @ X34 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X32 @ X33 ) @ ( k9_relat_1 @ X32 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('131',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k9_relat_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( r2_hidden @ X3 @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['86','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['85','139'])).

thf('141',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','140'])).

thf('142',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k6_subset_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['83','142'])).

thf('144',plain,(
    ! [X20: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('145',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('148',plain,(
    ! [X17: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('149',plain,
    ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['147','148'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('150',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v2_funct_1 @ X46 )
      | ~ ( r1_tarski @ X44 @ ( k1_relat_1 @ X46 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X46 @ X44 ) @ ( k9_relat_1 @ X46 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ k1_xboole_0 )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','160'])).

thf('162',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X17: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k10_relat_1 @ X35 @ ( k6_subset_1 @ X36 @ X37 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X35 @ X36 ) @ ( k10_relat_1 @ X35 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ X1 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('172',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) )
      = ( k10_relat_1 @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['170','171','172','173'])).

thf('175',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('176',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k2_relat_1 @ sk_B ) ) ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['174','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) )
      = ( k10_relat_1 @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['170','171','172','173'])).

thf('180',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('186',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('188',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('191',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['186','191','192','193'])).

thf('195',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k9_relat_1 @ X43 @ ( k10_relat_1 @ X43 @ X42 ) )
        = ( k3_xboole_0 @ X42 @ ( k9_relat_1 @ X43 @ ( k1_relat_1 @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v2_funct_1 @ X46 )
      | ~ ( r1_tarski @ X44 @ ( k1_relat_1 @ X46 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X46 @ X44 ) @ ( k9_relat_1 @ X46 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ X1 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) )
      = ( k10_relat_1 @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['170','171','172','173'])).

thf('203',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['201','206','207','208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['22','210'])).

thf('212',plain,(
    $false ),
    inference(demod,[status(thm)],['8','211'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RqjsLCQxTJ
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:24:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 4.67/4.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.67/4.91  % Solved by: fo/fo7.sh
% 4.67/4.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.67/4.91  % done 2343 iterations in 4.438s
% 4.67/4.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.67/4.91  % SZS output start Refutation
% 4.67/4.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.67/4.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.67/4.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.67/4.91  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.67/4.91  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.67/4.91  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 4.67/4.91  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.67/4.91  thf(sk_B_type, type, sk_B: $i).
% 4.67/4.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.67/4.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.67/4.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.67/4.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.67/4.91  thf(sk_A_type, type, sk_A: $i).
% 4.67/4.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.67/4.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.67/4.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.67/4.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.67/4.91  thf(t164_funct_1, conjecture,
% 4.67/4.91    (![A:$i,B:$i]:
% 4.67/4.91     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.67/4.91       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 4.67/4.91         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 4.67/4.91  thf(zf_stmt_0, negated_conjecture,
% 4.67/4.91    (~( ![A:$i,B:$i]:
% 4.67/4.91        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.67/4.91          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 4.67/4.91            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 4.67/4.91    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 4.67/4.91  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf(t146_funct_1, axiom,
% 4.67/4.91    (![A:$i,B:$i]:
% 4.67/4.91     ( ( v1_relat_1 @ B ) =>
% 4.67/4.91       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 4.67/4.91         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 4.67/4.91  thf('1', plain,
% 4.67/4.91      (![X38 : $i, X39 : $i]:
% 4.67/4.91         (~ (r1_tarski @ X38 @ (k1_relat_1 @ X39))
% 4.67/4.91          | (r1_tarski @ X38 @ (k10_relat_1 @ X39 @ (k9_relat_1 @ X39 @ X38)))
% 4.67/4.91          | ~ (v1_relat_1 @ X39))),
% 4.67/4.91      inference('cnf', [status(esa)], [t146_funct_1])).
% 4.67/4.91  thf('2', plain,
% 4.67/4.91      ((~ (v1_relat_1 @ sk_B)
% 4.67/4.91        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 4.67/4.91      inference('sup-', [status(thm)], ['0', '1'])).
% 4.67/4.91  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('4', plain,
% 4.67/4.91      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 4.67/4.91      inference('demod', [status(thm)], ['2', '3'])).
% 4.67/4.91  thf(d10_xboole_0, axiom,
% 4.67/4.91    (![A:$i,B:$i]:
% 4.67/4.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.67/4.91  thf('5', plain,
% 4.67/4.91      (![X12 : $i, X14 : $i]:
% 4.67/4.91         (((X12) = (X14))
% 4.67/4.91          | ~ (r1_tarski @ X14 @ X12)
% 4.67/4.91          | ~ (r1_tarski @ X12 @ X14))),
% 4.67/4.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.67/4.91  thf('6', plain,
% 4.67/4.91      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 4.67/4.91        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['4', '5'])).
% 4.67/4.91  thf('7', plain,
% 4.67/4.91      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('8', plain,
% 4.67/4.91      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 4.67/4.91      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 4.67/4.91  thf(t48_xboole_1, axiom,
% 4.67/4.91    (![A:$i,B:$i]:
% 4.67/4.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.67/4.91  thf('9', plain,
% 4.67/4.91      (![X18 : $i, X19 : $i]:
% 4.67/4.91         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 4.67/4.91           = (k3_xboole_0 @ X18 @ X19))),
% 4.67/4.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.67/4.91  thf(redefinition_k6_subset_1, axiom,
% 4.67/4.91    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.67/4.91  thf('10', plain,
% 4.67/4.91      (![X23 : $i, X24 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.67/4.91  thf('11', plain,
% 4.67/4.91      (![X23 : $i, X24 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.67/4.91  thf('12', plain,
% 4.67/4.91      (![X18 : $i, X19 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 4.67/4.91           = (k3_xboole_0 @ X18 @ X19))),
% 4.67/4.91      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.67/4.91  thf(d3_tarski, axiom,
% 4.67/4.91    (![A:$i,B:$i]:
% 4.67/4.91     ( ( r1_tarski @ A @ B ) <=>
% 4.67/4.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.67/4.91  thf('13', plain,
% 4.67/4.91      (![X3 : $i, X5 : $i]:
% 4.67/4.91         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_tarski])).
% 4.67/4.91  thf(d5_xboole_0, axiom,
% 4.67/4.91    (![A:$i,B:$i,C:$i]:
% 4.67/4.91     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.67/4.91       ( ![D:$i]:
% 4.67/4.91         ( ( r2_hidden @ D @ C ) <=>
% 4.67/4.91           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.67/4.91  thf('14', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.67/4.91         (~ (r2_hidden @ X10 @ X9)
% 4.67/4.91          | (r2_hidden @ X10 @ X7)
% 4.67/4.91          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 4.67/4.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.67/4.91  thf('15', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.67/4.91         ((r2_hidden @ X10 @ X7)
% 4.67/4.91          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 4.67/4.91      inference('simplify', [status(thm)], ['14'])).
% 4.67/4.91  thf('16', plain,
% 4.67/4.91      (![X23 : $i, X24 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.67/4.91  thf('17', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.67/4.91         ((r2_hidden @ X10 @ X7)
% 4.67/4.91          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 4.67/4.91      inference('demod', [status(thm)], ['15', '16'])).
% 4.67/4.91  thf('18', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.67/4.91         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 4.67/4.91          | (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X1))),
% 4.67/4.91      inference('sup-', [status(thm)], ['13', '17'])).
% 4.67/4.91  thf('19', plain,
% 4.67/4.91      (![X3 : $i, X5 : $i]:
% 4.67/4.91         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_tarski])).
% 4.67/4.91  thf('20', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)
% 4.67/4.91          | (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0))),
% 4.67/4.91      inference('sup-', [status(thm)], ['18', '19'])).
% 4.67/4.91  thf('21', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 4.67/4.91      inference('simplify', [status(thm)], ['20'])).
% 4.67/4.91  thf('22', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.67/4.91      inference('sup+', [status(thm)], ['12', '21'])).
% 4.67/4.91  thf(t146_relat_1, axiom,
% 4.67/4.91    (![A:$i]:
% 4.67/4.91     ( ( v1_relat_1 @ A ) =>
% 4.67/4.91       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 4.67/4.91  thf('23', plain,
% 4.67/4.91      (![X27 : $i]:
% 4.67/4.91         (((k9_relat_1 @ X27 @ (k1_relat_1 @ X27)) = (k2_relat_1 @ X27))
% 4.67/4.91          | ~ (v1_relat_1 @ X27))),
% 4.67/4.91      inference('cnf', [status(esa)], [t146_relat_1])).
% 4.67/4.91  thf('24', plain,
% 4.67/4.91      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 4.67/4.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.67/4.91  thf('25', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 4.67/4.91      inference('simplify', [status(thm)], ['24'])).
% 4.67/4.91  thf('26', plain,
% 4.67/4.91      (![X38 : $i, X39 : $i]:
% 4.67/4.91         (~ (r1_tarski @ X38 @ (k1_relat_1 @ X39))
% 4.67/4.91          | (r1_tarski @ X38 @ (k10_relat_1 @ X39 @ (k9_relat_1 @ X39 @ X38)))
% 4.67/4.91          | ~ (v1_relat_1 @ X39))),
% 4.67/4.91      inference('cnf', [status(esa)], [t146_funct_1])).
% 4.67/4.91  thf('27', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (~ (v1_relat_1 @ X0)
% 4.67/4.91          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 4.67/4.91             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 4.67/4.91      inference('sup-', [status(thm)], ['25', '26'])).
% 4.67/4.91  thf('28', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 4.67/4.91           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 4.67/4.91          | ~ (v1_relat_1 @ X0)
% 4.67/4.91          | ~ (v1_relat_1 @ X0))),
% 4.67/4.91      inference('sup+', [status(thm)], ['23', '27'])).
% 4.67/4.91  thf('29', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (~ (v1_relat_1 @ X0)
% 4.67/4.91          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 4.67/4.91             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['28'])).
% 4.67/4.91  thf(t167_relat_1, axiom,
% 4.67/4.91    (![A:$i,B:$i]:
% 4.67/4.91     ( ( v1_relat_1 @ B ) =>
% 4.67/4.91       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 4.67/4.91  thf('30', plain,
% 4.67/4.91      (![X28 : $i, X29 : $i]:
% 4.67/4.91         ((r1_tarski @ (k10_relat_1 @ X28 @ X29) @ (k1_relat_1 @ X28))
% 4.67/4.91          | ~ (v1_relat_1 @ X28))),
% 4.67/4.91      inference('cnf', [status(esa)], [t167_relat_1])).
% 4.67/4.91  thf('31', plain,
% 4.67/4.91      (![X3 : $i, X5 : $i]:
% 4.67/4.91         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_tarski])).
% 4.67/4.91  thf('32', plain,
% 4.67/4.91      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 4.67/4.91         (~ (r2_hidden @ X6 @ X7)
% 4.67/4.91          | (r2_hidden @ X6 @ X8)
% 4.67/4.91          | (r2_hidden @ X6 @ X9)
% 4.67/4.91          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 4.67/4.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.67/4.91  thf('33', plain,
% 4.67/4.91      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.67/4.91         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 4.67/4.91          | (r2_hidden @ X6 @ X8)
% 4.67/4.91          | ~ (r2_hidden @ X6 @ X7))),
% 4.67/4.91      inference('simplify', [status(thm)], ['32'])).
% 4.67/4.91  thf('34', plain,
% 4.67/4.91      (![X23 : $i, X24 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.67/4.91  thf('35', plain,
% 4.67/4.91      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.67/4.91         ((r2_hidden @ X6 @ (k6_subset_1 @ X7 @ X8))
% 4.67/4.91          | (r2_hidden @ X6 @ X8)
% 4.67/4.91          | ~ (r2_hidden @ X6 @ X7))),
% 4.67/4.91      inference('demod', [status(thm)], ['33', '34'])).
% 4.67/4.91  thf('36', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.67/4.91         ((r1_tarski @ X0 @ X1)
% 4.67/4.91          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 4.67/4.91          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k6_subset_1 @ X0 @ X2)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['31', '35'])).
% 4.67/4.91  thf('37', plain,
% 4.67/4.91      (![X3 : $i, X5 : $i]:
% 4.67/4.91         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_tarski])).
% 4.67/4.91  thf('38', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((r2_hidden @ (sk_C @ (k6_subset_1 @ X1 @ X0) @ X1) @ X0)
% 4.67/4.91          | (r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0))
% 4.67/4.91          | (r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['36', '37'])).
% 4.67/4.91  thf('39', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0))
% 4.67/4.91          | (r2_hidden @ (sk_C @ (k6_subset_1 @ X1 @ X0) @ X1) @ X0))),
% 4.67/4.91      inference('simplify', [status(thm)], ['38'])).
% 4.67/4.91  thf('40', plain,
% 4.67/4.91      (![X3 : $i, X5 : $i]:
% 4.67/4.91         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_tarski])).
% 4.67/4.91  thf('41', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.67/4.91         (~ (r2_hidden @ X10 @ X9)
% 4.67/4.91          | ~ (r2_hidden @ X10 @ X8)
% 4.67/4.91          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 4.67/4.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.67/4.91  thf('42', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.67/4.91         (~ (r2_hidden @ X10 @ X8)
% 4.67/4.91          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 4.67/4.91      inference('simplify', [status(thm)], ['41'])).
% 4.67/4.91  thf('43', plain,
% 4.67/4.91      (![X23 : $i, X24 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.67/4.91  thf('44', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.67/4.91         (~ (r2_hidden @ X10 @ X8)
% 4.67/4.91          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 4.67/4.91      inference('demod', [status(thm)], ['42', '43'])).
% 4.67/4.91  thf('45', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.67/4.91         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 4.67/4.91          | ~ (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X0))),
% 4.67/4.91      inference('sup-', [status(thm)], ['40', '44'])).
% 4.67/4.91  thf('46', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ 
% 4.67/4.91           (k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X0))
% 4.67/4.91          | (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ 
% 4.67/4.91             (k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X0)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['39', '45'])).
% 4.67/4.91  thf('47', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ 
% 4.67/4.91          (k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X0))),
% 4.67/4.91      inference('simplify', [status(thm)], ['46'])).
% 4.67/4.91  thf('48', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 4.67/4.91      inference('simplify', [status(thm)], ['20'])).
% 4.67/4.91  thf('49', plain,
% 4.67/4.91      (![X12 : $i, X14 : $i]:
% 4.67/4.91         (((X12) = (X14))
% 4.67/4.91          | ~ (r1_tarski @ X14 @ X12)
% 4.67/4.91          | ~ (r1_tarski @ X12 @ X14))),
% 4.67/4.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.67/4.91  thf('50', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 4.67/4.91          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['48', '49'])).
% 4.67/4.91  thf('51', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X1 @ X0)
% 4.67/4.91           = (k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X0))),
% 4.67/4.91      inference('sup-', [status(thm)], ['47', '50'])).
% 4.67/4.91  thf('52', plain,
% 4.67/4.91      (![X18 : $i, X19 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 4.67/4.91           = (k3_xboole_0 @ X18 @ X19))),
% 4.67/4.91      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.67/4.91  thf('53', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0))
% 4.67/4.91           = (k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X0))),
% 4.67/4.91      inference('sup+', [status(thm)], ['51', '52'])).
% 4.67/4.91  thf(t3_boole, axiom,
% 4.67/4.91    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.67/4.91  thf('54', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 4.67/4.91      inference('cnf', [status(esa)], [t3_boole])).
% 4.67/4.91  thf('55', plain,
% 4.67/4.91      (![X23 : $i, X24 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.67/4.91  thf('56', plain, (![X16 : $i]: ((k6_subset_1 @ X16 @ k1_xboole_0) = (X16))),
% 4.67/4.91      inference('demod', [status(thm)], ['54', '55'])).
% 4.67/4.91  thf('57', plain,
% 4.67/4.91      (![X18 : $i, X19 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 4.67/4.91           = (k3_xboole_0 @ X18 @ X19))),
% 4.67/4.91      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.67/4.91  thf('58', plain,
% 4.67/4.91      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 4.67/4.91      inference('sup+', [status(thm)], ['56', '57'])).
% 4.67/4.91  thf('59', plain,
% 4.67/4.91      (![X18 : $i, X19 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 4.67/4.91           = (k3_xboole_0 @ X18 @ X19))),
% 4.67/4.91      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.67/4.91  thf(t4_boole, axiom,
% 4.67/4.91    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 4.67/4.91  thf('60', plain,
% 4.67/4.91      (![X20 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 4.67/4.91      inference('cnf', [status(esa)], [t4_boole])).
% 4.67/4.91  thf('61', plain,
% 4.67/4.91      (![X23 : $i, X24 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.67/4.91  thf('62', plain,
% 4.67/4.91      (![X20 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 4.67/4.91      inference('demod', [status(thm)], ['60', '61'])).
% 4.67/4.91  thf('63', plain,
% 4.67/4.91      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.67/4.91      inference('sup+', [status(thm)], ['59', '62'])).
% 4.67/4.91  thf(commutativity_k3_xboole_0, axiom,
% 4.67/4.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.67/4.91  thf('64', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.67/4.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.67/4.91  thf('65', plain,
% 4.67/4.91      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.67/4.91      inference('sup+', [status(thm)], ['63', '64'])).
% 4.67/4.91  thf('66', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 4.67/4.91      inference('demod', [status(thm)], ['58', '65'])).
% 4.67/4.91  thf('67', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.67/4.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.67/4.91  thf('68', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 4.67/4.91      inference('demod', [status(thm)], ['53', '66', '67'])).
% 4.67/4.91  thf('69', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.67/4.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.67/4.91  thf('70', plain,
% 4.67/4.91      (![X27 : $i]:
% 4.67/4.91         (((k9_relat_1 @ X27 @ (k1_relat_1 @ X27)) = (k2_relat_1 @ X27))
% 4.67/4.91          | ~ (v1_relat_1 @ X27))),
% 4.67/4.91      inference('cnf', [status(esa)], [t146_relat_1])).
% 4.67/4.91  thf(t148_funct_1, axiom,
% 4.67/4.91    (![A:$i,B:$i]:
% 4.67/4.91     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.67/4.91       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 4.67/4.91         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 4.67/4.91  thf('71', plain,
% 4.67/4.91      (![X42 : $i, X43 : $i]:
% 4.67/4.91         (((k9_relat_1 @ X43 @ (k10_relat_1 @ X43 @ X42))
% 4.67/4.91            = (k3_xboole_0 @ X42 @ (k9_relat_1 @ X43 @ (k1_relat_1 @ X43))))
% 4.67/4.91          | ~ (v1_funct_1 @ X43)
% 4.67/4.91          | ~ (v1_relat_1 @ X43))),
% 4.67/4.91      inference('cnf', [status(esa)], [t148_funct_1])).
% 4.67/4.91  thf('72', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 4.67/4.91            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 4.67/4.91          | ~ (v1_relat_1 @ X0)
% 4.67/4.91          | ~ (v1_relat_1 @ X0)
% 4.67/4.91          | ~ (v1_funct_1 @ X0))),
% 4.67/4.91      inference('sup+', [status(thm)], ['70', '71'])).
% 4.67/4.91  thf('73', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         (~ (v1_funct_1 @ X0)
% 4.67/4.91          | ~ (v1_relat_1 @ X0)
% 4.67/4.91          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 4.67/4.91              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['72'])).
% 4.67/4.91  thf('74', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 4.67/4.91      inference('demod', [status(thm)], ['58', '65'])).
% 4.67/4.91  thf(t138_funct_1, axiom,
% 4.67/4.91    (![A:$i,B:$i,C:$i]:
% 4.67/4.91     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.67/4.91       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 4.67/4.91         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 4.67/4.91  thf('75', plain,
% 4.67/4.91      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.67/4.91         (((k10_relat_1 @ X35 @ (k6_subset_1 @ X36 @ X37))
% 4.67/4.91            = (k6_subset_1 @ (k10_relat_1 @ X35 @ X36) @ 
% 4.67/4.91               (k10_relat_1 @ X35 @ X37)))
% 4.67/4.91          | ~ (v1_funct_1 @ X35)
% 4.67/4.91          | ~ (v1_relat_1 @ X35))),
% 4.67/4.91      inference('cnf', [status(esa)], [t138_funct_1])).
% 4.67/4.91  thf('76', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         (((k10_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0))
% 4.67/4.91          | ~ (v1_relat_1 @ X1)
% 4.67/4.91          | ~ (v1_funct_1 @ X1))),
% 4.67/4.91      inference('sup+', [status(thm)], ['74', '75'])).
% 4.67/4.91  thf('77', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 4.67/4.91      inference('demod', [status(thm)], ['58', '65'])).
% 4.67/4.91  thf('78', plain,
% 4.67/4.91      (![X1 : $i]:
% 4.67/4.91         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 4.67/4.91          | ~ (v1_relat_1 @ X1)
% 4.67/4.91          | ~ (v1_funct_1 @ X1))),
% 4.67/4.91      inference('demod', [status(thm)], ['76', '77'])).
% 4.67/4.91  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.67/4.91  thf('79', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 4.67/4.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.67/4.91  thf(t147_funct_1, axiom,
% 4.67/4.91    (![A:$i,B:$i]:
% 4.67/4.91     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.67/4.91       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 4.67/4.91         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 4.67/4.91  thf('80', plain,
% 4.67/4.91      (![X40 : $i, X41 : $i]:
% 4.67/4.91         (~ (r1_tarski @ X40 @ (k2_relat_1 @ X41))
% 4.67/4.91          | ((k9_relat_1 @ X41 @ (k10_relat_1 @ X41 @ X40)) = (X40))
% 4.67/4.91          | ~ (v1_funct_1 @ X41)
% 4.67/4.91          | ~ (v1_relat_1 @ X41))),
% 4.67/4.91      inference('cnf', [status(esa)], [t147_funct_1])).
% 4.67/4.91  thf('81', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (~ (v1_relat_1 @ X0)
% 4.67/4.91          | ~ (v1_funct_1 @ X0)
% 4.67/4.91          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 4.67/4.91              = (k1_xboole_0)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['79', '80'])).
% 4.67/4.91  thf('82', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 4.67/4.91          | ~ (v1_funct_1 @ X0)
% 4.67/4.91          | ~ (v1_relat_1 @ X0)
% 4.67/4.91          | ~ (v1_funct_1 @ X0)
% 4.67/4.91          | ~ (v1_relat_1 @ X0))),
% 4.67/4.91      inference('sup+', [status(thm)], ['78', '81'])).
% 4.67/4.91  thf('83', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (~ (v1_relat_1 @ X0)
% 4.67/4.91          | ~ (v1_funct_1 @ X0)
% 4.67/4.91          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 4.67/4.91      inference('simplify', [status(thm)], ['82'])).
% 4.67/4.91  thf('84', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0))
% 4.67/4.91          | (r2_hidden @ (sk_C @ (k6_subset_1 @ X1 @ X0) @ X1) @ X0))),
% 4.67/4.91      inference('simplify', [status(thm)], ['38'])).
% 4.67/4.91  thf('85', plain,
% 4.67/4.91      (![X3 : $i, X5 : $i]:
% 4.67/4.91         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_tarski])).
% 4.67/4.91  thf('86', plain,
% 4.67/4.91      (![X27 : $i]:
% 4.67/4.91         (((k9_relat_1 @ X27 @ (k1_relat_1 @ X27)) = (k2_relat_1 @ X27))
% 4.67/4.91          | ~ (v1_relat_1 @ X27))),
% 4.67/4.91      inference('cnf', [status(esa)], [t146_relat_1])).
% 4.67/4.91  thf('87', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X11 : $i]:
% 4.67/4.91         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 4.67/4.91          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 4.67/4.91          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 4.67/4.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.67/4.91  thf('88', plain,
% 4.67/4.91      (![X23 : $i, X24 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.67/4.91  thf('89', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X11 : $i]:
% 4.67/4.91         (((X11) = (k6_subset_1 @ X7 @ X8))
% 4.67/4.91          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 4.67/4.91          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 4.67/4.91      inference('demod', [status(thm)], ['87', '88'])).
% 4.67/4.91  thf('90', plain, (![X16 : $i]: ((k6_subset_1 @ X16 @ k1_xboole_0) = (X16))),
% 4.67/4.91      inference('demod', [status(thm)], ['54', '55'])).
% 4.67/4.91  thf('91', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.67/4.91         (~ (r2_hidden @ X10 @ X8)
% 4.67/4.91          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 4.67/4.91      inference('demod', [status(thm)], ['42', '43'])).
% 4.67/4.91  thf('92', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 4.67/4.91      inference('sup-', [status(thm)], ['90', '91'])).
% 4.67/4.91  thf('93', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.67/4.91      inference('condensation', [status(thm)], ['92'])).
% 4.67/4.91  thf('94', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 4.67/4.91          | ((X1) = (k6_subset_1 @ k1_xboole_0 @ X0)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['89', '93'])).
% 4.67/4.91  thf('95', plain,
% 4.67/4.91      (![X20 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 4.67/4.91      inference('demod', [status(thm)], ['60', '61'])).
% 4.67/4.91  thf('96', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 4.67/4.91          | ((X1) = (k1_xboole_0)))),
% 4.67/4.91      inference('demod', [status(thm)], ['94', '95'])).
% 4.67/4.91  thf('97', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X11 : $i]:
% 4.67/4.91         (((X11) = (k6_subset_1 @ X7 @ X8))
% 4.67/4.91          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 4.67/4.91          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 4.67/4.91      inference('demod', [status(thm)], ['87', '88'])).
% 4.67/4.91  thf('98', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.67/4.91      inference('condensation', [status(thm)], ['92'])).
% 4.67/4.91  thf('99', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 4.67/4.91          | ((k1_xboole_0) = (k6_subset_1 @ X0 @ X1)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['97', '98'])).
% 4.67/4.91  thf('100', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('101', plain,
% 4.67/4.91      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.67/4.91         (~ (r2_hidden @ X2 @ X3)
% 4.67/4.91          | (r2_hidden @ X2 @ X4)
% 4.67/4.91          | ~ (r1_tarski @ X3 @ X4))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_tarski])).
% 4.67/4.91  thf('102', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 4.67/4.91      inference('sup-', [status(thm)], ['100', '101'])).
% 4.67/4.91  thf('103', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (((k1_xboole_0) = (k6_subset_1 @ sk_A @ X0))
% 4.67/4.91          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['99', '102'])).
% 4.67/4.91  thf('104', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X11 : $i]:
% 4.67/4.91         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 4.67/4.91          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 4.67/4.91          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 4.67/4.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.67/4.91  thf('105', plain,
% 4.67/4.91      (![X23 : $i, X24 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.67/4.91  thf('106', plain,
% 4.67/4.91      (![X7 : $i, X8 : $i, X11 : $i]:
% 4.67/4.91         (((X11) = (k6_subset_1 @ X7 @ X8))
% 4.67/4.91          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 4.67/4.91          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 4.67/4.91      inference('demod', [status(thm)], ['104', '105'])).
% 4.67/4.91  thf('107', plain,
% 4.67/4.91      ((((k1_xboole_0) = (k6_subset_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 4.67/4.91        | (r2_hidden @ (sk_D @ k1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 4.67/4.91           k1_xboole_0)
% 4.67/4.91        | ((k1_xboole_0) = (k6_subset_1 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 4.67/4.91      inference('sup-', [status(thm)], ['103', '106'])).
% 4.67/4.91  thf('108', plain,
% 4.67/4.91      (((r2_hidden @ (sk_D @ k1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 4.67/4.91         k1_xboole_0)
% 4.67/4.91        | ((k1_xboole_0) = (k6_subset_1 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['107'])).
% 4.67/4.91  thf('109', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.67/4.91      inference('condensation', [status(thm)], ['92'])).
% 4.67/4.91  thf('110', plain,
% 4.67/4.91      (((k1_xboole_0) = (k6_subset_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 4.67/4.91      inference('clc', [status(thm)], ['108', '109'])).
% 4.67/4.91  thf('111', plain,
% 4.67/4.91      (![X18 : $i, X19 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 4.67/4.91           = (k3_xboole_0 @ X18 @ X19))),
% 4.67/4.91      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.67/4.91  thf('112', plain,
% 4.67/4.91      (((k6_subset_1 @ sk_A @ k1_xboole_0)
% 4.67/4.91         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 4.67/4.91      inference('sup+', [status(thm)], ['110', '111'])).
% 4.67/4.91  thf('113', plain, (![X16 : $i]: ((k6_subset_1 @ X16 @ k1_xboole_0) = (X16))),
% 4.67/4.91      inference('demod', [status(thm)], ['54', '55'])).
% 4.67/4.91  thf('114', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 4.67/4.91      inference('demod', [status(thm)], ['112', '113'])).
% 4.67/4.91  thf('115', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.67/4.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.67/4.91  thf('116', plain,
% 4.67/4.91      (![X18 : $i, X19 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 4.67/4.91           = (k3_xboole_0 @ X18 @ X19))),
% 4.67/4.91      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.67/4.91  thf('117', plain,
% 4.67/4.91      (![X18 : $i, X19 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 4.67/4.91           = (k3_xboole_0 @ X18 @ X19))),
% 4.67/4.91      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.67/4.91  thf('118', plain,
% 4.67/4.91      (![X0 : $i, X1 : $i]:
% 4.67/4.91         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.67/4.91           = (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 4.67/4.92      inference('sup+', [status(thm)], ['116', '117'])).
% 4.67/4.92  thf('119', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         ((k6_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 4.67/4.92           = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 4.67/4.92      inference('sup+', [status(thm)], ['115', '118'])).
% 4.67/4.92  thf('120', plain,
% 4.67/4.92      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)
% 4.67/4.92         = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 4.67/4.92            (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 4.67/4.92      inference('sup+', [status(thm)], ['114', '119'])).
% 4.67/4.92  thf('121', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.67/4.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.67/4.92  thf('122', plain,
% 4.67/4.92      (![X18 : $i, X19 : $i]:
% 4.67/4.92         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 4.67/4.92           = (k3_xboole_0 @ X18 @ X19))),
% 4.67/4.92      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.67/4.92  thf('123', plain,
% 4.67/4.92      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.67/4.92         (~ (r2_hidden @ X10 @ X8)
% 4.67/4.92          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 4.67/4.92      inference('demod', [status(thm)], ['42', '43'])).
% 4.67/4.92  thf('124', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.67/4.92         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 4.67/4.92          | ~ (r2_hidden @ X2 @ (k6_subset_1 @ X1 @ X0)))),
% 4.67/4.92      inference('sup-', [status(thm)], ['122', '123'])).
% 4.67/4.92  thf('125', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.67/4.92         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 4.67/4.92          | ~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 4.67/4.92      inference('sup-', [status(thm)], ['121', '124'])).
% 4.67/4.92  thf('126', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (r2_hidden @ X0 @ (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))
% 4.67/4.92          | ~ (r2_hidden @ X0 @ 
% 4.67/4.92               (k6_subset_1 @ (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 4.67/4.92                (k1_relat_1 @ sk_B))))),
% 4.67/4.92      inference('sup-', [status(thm)], ['120', '125'])).
% 4.67/4.92  thf('127', plain,
% 4.67/4.92      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.67/4.92         ((r2_hidden @ X10 @ X7)
% 4.67/4.92          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 4.67/4.92      inference('demod', [status(thm)], ['15', '16'])).
% 4.67/4.92  thf('128', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         ~ (r2_hidden @ X0 @ 
% 4.67/4.92            (k6_subset_1 @ (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 4.67/4.92             (k1_relat_1 @ sk_B)))),
% 4.67/4.92      inference('clc', [status(thm)], ['126', '127'])).
% 4.67/4.92  thf('129', plain,
% 4.67/4.92      (((k6_subset_1 @ (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 4.67/4.92         (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 4.67/4.92      inference('sup-', [status(thm)], ['96', '128'])).
% 4.67/4.92  thf(t123_funct_1, axiom,
% 4.67/4.92    (![A:$i,B:$i,C:$i]:
% 4.67/4.92     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.67/4.92       ( ( v2_funct_1 @ C ) =>
% 4.67/4.92         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 4.67/4.92           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 4.67/4.92  thf('130', plain,
% 4.67/4.92      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.67/4.92         (~ (v2_funct_1 @ X32)
% 4.67/4.92          | ((k9_relat_1 @ X32 @ (k6_subset_1 @ X33 @ X34))
% 4.67/4.92              = (k6_subset_1 @ (k9_relat_1 @ X32 @ X33) @ 
% 4.67/4.92                 (k9_relat_1 @ X32 @ X34)))
% 4.67/4.92          | ~ (v1_funct_1 @ X32)
% 4.67/4.92          | ~ (v1_relat_1 @ X32))),
% 4.67/4.92      inference('cnf', [status(esa)], [t123_funct_1])).
% 4.67/4.92  thf('131', plain,
% 4.67/4.92      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.67/4.92         (~ (r2_hidden @ X10 @ X8)
% 4.67/4.92          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 4.67/4.92      inference('demod', [status(thm)], ['42', '43'])).
% 4.67/4.92  thf('132', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.67/4.92         (~ (r2_hidden @ X3 @ (k9_relat_1 @ X2 @ (k6_subset_1 @ X1 @ X0)))
% 4.67/4.92          | ~ (v1_relat_1 @ X2)
% 4.67/4.92          | ~ (v1_funct_1 @ X2)
% 4.67/4.92          | ~ (v2_funct_1 @ X2)
% 4.67/4.92          | ~ (r2_hidden @ X3 @ (k9_relat_1 @ X2 @ X0)))),
% 4.67/4.92      inference('sup-', [status(thm)], ['130', '131'])).
% 4.67/4.92  thf('133', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         (~ (r2_hidden @ X1 @ (k9_relat_1 @ X0 @ k1_xboole_0))
% 4.67/4.92          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 4.67/4.92          | ~ (v2_funct_1 @ X0)
% 4.67/4.92          | ~ (v1_funct_1 @ X0)
% 4.67/4.92          | ~ (v1_relat_1 @ X0))),
% 4.67/4.92      inference('sup-', [status(thm)], ['129', '132'])).
% 4.67/4.92  thf('134', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 4.67/4.92          | ~ (v1_relat_1 @ sk_B)
% 4.67/4.92          | ~ (v1_relat_1 @ sk_B)
% 4.67/4.92          | ~ (v1_funct_1 @ sk_B)
% 4.67/4.92          | ~ (v2_funct_1 @ sk_B)
% 4.67/4.92          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_B @ k1_xboole_0)))),
% 4.67/4.92      inference('sup-', [status(thm)], ['86', '133'])).
% 4.67/4.92  thf('135', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('136', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('137', plain, ((v1_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('138', plain, ((v2_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('139', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 4.67/4.92          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_B @ k1_xboole_0)))),
% 4.67/4.92      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 4.67/4.92  thf('140', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         ((r1_tarski @ (k9_relat_1 @ sk_B @ k1_xboole_0) @ X0)
% 4.67/4.92          | ~ (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_B @ k1_xboole_0)) @ 
% 4.67/4.92               (k2_relat_1 @ sk_B)))),
% 4.67/4.92      inference('sup-', [status(thm)], ['85', '139'])).
% 4.67/4.92  thf('141', plain,
% 4.67/4.92      (((r1_tarski @ (k9_relat_1 @ sk_B @ k1_xboole_0) @ 
% 4.67/4.92         (k6_subset_1 @ (k9_relat_1 @ sk_B @ k1_xboole_0) @ (k2_relat_1 @ sk_B)))
% 4.67/4.92        | (r1_tarski @ (k9_relat_1 @ sk_B @ k1_xboole_0) @ 
% 4.67/4.92           (k6_subset_1 @ (k9_relat_1 @ sk_B @ k1_xboole_0) @ 
% 4.67/4.92            (k2_relat_1 @ sk_B))))),
% 4.67/4.92      inference('sup-', [status(thm)], ['84', '140'])).
% 4.67/4.92  thf('142', plain,
% 4.67/4.92      ((r1_tarski @ (k9_relat_1 @ sk_B @ k1_xboole_0) @ 
% 4.67/4.92        (k6_subset_1 @ (k9_relat_1 @ sk_B @ k1_xboole_0) @ (k2_relat_1 @ sk_B)))),
% 4.67/4.92      inference('simplify', [status(thm)], ['141'])).
% 4.67/4.92  thf('143', plain,
% 4.67/4.92      (((r1_tarski @ (k9_relat_1 @ sk_B @ k1_xboole_0) @ 
% 4.67/4.92         (k6_subset_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_B)))
% 4.67/4.92        | ~ (v1_funct_1 @ sk_B)
% 4.67/4.92        | ~ (v1_relat_1 @ sk_B))),
% 4.67/4.92      inference('sup+', [status(thm)], ['83', '142'])).
% 4.67/4.92  thf('144', plain,
% 4.67/4.92      (![X20 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 4.67/4.92      inference('demod', [status(thm)], ['60', '61'])).
% 4.67/4.92  thf('145', plain, ((v1_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('146', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('147', plain,
% 4.67/4.92      ((r1_tarski @ (k9_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0)),
% 4.67/4.92      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 4.67/4.92  thf(t3_xboole_1, axiom,
% 4.67/4.92    (![A:$i]:
% 4.67/4.92     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.67/4.92  thf('148', plain,
% 4.67/4.92      (![X17 : $i]:
% 4.67/4.92         (((X17) = (k1_xboole_0)) | ~ (r1_tarski @ X17 @ k1_xboole_0))),
% 4.67/4.92      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.67/4.92  thf('149', plain, (((k9_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 4.67/4.92      inference('sup-', [status(thm)], ['147', '148'])).
% 4.67/4.92  thf(t157_funct_1, axiom,
% 4.67/4.92    (![A:$i,B:$i,C:$i]:
% 4.67/4.92     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.67/4.92       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 4.67/4.92           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 4.67/4.92         ( r1_tarski @ A @ B ) ) ))).
% 4.67/4.92  thf('150', plain,
% 4.67/4.92      (![X44 : $i, X45 : $i, X46 : $i]:
% 4.67/4.92         ((r1_tarski @ X44 @ X45)
% 4.67/4.92          | ~ (v1_relat_1 @ X46)
% 4.67/4.92          | ~ (v1_funct_1 @ X46)
% 4.67/4.92          | ~ (v2_funct_1 @ X46)
% 4.67/4.92          | ~ (r1_tarski @ X44 @ (k1_relat_1 @ X46))
% 4.67/4.92          | ~ (r1_tarski @ (k9_relat_1 @ X46 @ X44) @ (k9_relat_1 @ X46 @ X45)))),
% 4.67/4.92      inference('cnf', [status(esa)], [t157_funct_1])).
% 4.67/4.92  thf('151', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ k1_xboole_0)
% 4.67/4.92          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 4.67/4.92          | ~ (v2_funct_1 @ sk_B)
% 4.67/4.92          | ~ (v1_funct_1 @ sk_B)
% 4.67/4.92          | ~ (v1_relat_1 @ sk_B)
% 4.67/4.92          | (r1_tarski @ X0 @ k1_xboole_0))),
% 4.67/4.92      inference('sup-', [status(thm)], ['149', '150'])).
% 4.67/4.92  thf('152', plain, ((v2_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('153', plain, ((v1_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('154', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('155', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ k1_xboole_0)
% 4.67/4.92          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 4.67/4.92          | (r1_tarski @ X0 @ k1_xboole_0))),
% 4.67/4.92      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 4.67/4.92  thf('156', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ k1_xboole_0)
% 4.67/4.92          | ~ (v1_relat_1 @ sk_B)
% 4.67/4.92          | ~ (v1_funct_1 @ sk_B)
% 4.67/4.92          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ k1_xboole_0)
% 4.67/4.92          | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B)))),
% 4.67/4.92      inference('sup-', [status(thm)], ['73', '155'])).
% 4.67/4.92  thf('157', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('158', plain, ((v1_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('159', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ k1_xboole_0)
% 4.67/4.92          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ k1_xboole_0)
% 4.67/4.92          | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B)))),
% 4.67/4.92      inference('demod', [status(thm)], ['156', '157', '158'])).
% 4.67/4.92  thf('160', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0) @ k1_xboole_0)
% 4.67/4.92          | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 4.67/4.92          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ k1_xboole_0))),
% 4.67/4.92      inference('sup-', [status(thm)], ['69', '159'])).
% 4.67/4.92  thf('161', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 4.67/4.92          | (r1_tarski @ 
% 4.67/4.92             (k10_relat_1 @ sk_B @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 4.67/4.92             k1_xboole_0)
% 4.67/4.92          | ~ (r1_tarski @ 
% 4.67/4.92               (k10_relat_1 @ sk_B @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 4.67/4.92               (k1_relat_1 @ sk_B)))),
% 4.67/4.92      inference('sup-', [status(thm)], ['68', '160'])).
% 4.67/4.92  thf('162', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 4.67/4.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.67/4.92  thf('163', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         ((r1_tarski @ 
% 4.67/4.92           (k10_relat_1 @ sk_B @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 4.67/4.92           k1_xboole_0)
% 4.67/4.92          | ~ (r1_tarski @ 
% 4.67/4.92               (k10_relat_1 @ sk_B @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 4.67/4.92               (k1_relat_1 @ sk_B)))),
% 4.67/4.92      inference('demod', [status(thm)], ['161', '162'])).
% 4.67/4.92  thf('164', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (v1_relat_1 @ sk_B)
% 4.67/4.92          | (r1_tarski @ 
% 4.67/4.92             (k10_relat_1 @ sk_B @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 4.67/4.92             k1_xboole_0))),
% 4.67/4.92      inference('sup-', [status(thm)], ['30', '163'])).
% 4.67/4.92  thf('165', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('166', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (r1_tarski @ 
% 4.67/4.92          (k10_relat_1 @ sk_B @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 4.67/4.92          k1_xboole_0)),
% 4.67/4.92      inference('demod', [status(thm)], ['164', '165'])).
% 4.67/4.92  thf('167', plain,
% 4.67/4.92      (![X17 : $i]:
% 4.67/4.92         (((X17) = (k1_xboole_0)) | ~ (r1_tarski @ X17 @ k1_xboole_0))),
% 4.67/4.92      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.67/4.92  thf('168', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         ((k10_relat_1 @ sk_B @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 4.67/4.92           = (k1_xboole_0))),
% 4.67/4.92      inference('sup-', [status(thm)], ['166', '167'])).
% 4.67/4.92  thf('169', plain,
% 4.67/4.92      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.67/4.92         (((k10_relat_1 @ X35 @ (k6_subset_1 @ X36 @ X37))
% 4.67/4.92            = (k6_subset_1 @ (k10_relat_1 @ X35 @ X36) @ 
% 4.67/4.92               (k10_relat_1 @ X35 @ X37)))
% 4.67/4.92          | ~ (v1_funct_1 @ X35)
% 4.67/4.92          | ~ (v1_relat_1 @ X35))),
% 4.67/4.92      inference('cnf', [status(esa)], [t138_funct_1])).
% 4.67/4.92  thf('170', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         (((k10_relat_1 @ sk_B @ 
% 4.67/4.92            (k6_subset_1 @ X1 @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))))
% 4.67/4.92            = (k6_subset_1 @ (k10_relat_1 @ sk_B @ X1) @ k1_xboole_0))
% 4.67/4.92          | ~ (v1_relat_1 @ sk_B)
% 4.67/4.92          | ~ (v1_funct_1 @ sk_B))),
% 4.67/4.92      inference('sup+', [status(thm)], ['168', '169'])).
% 4.67/4.92  thf('171', plain, (![X16 : $i]: ((k6_subset_1 @ X16 @ k1_xboole_0) = (X16))),
% 4.67/4.92      inference('demod', [status(thm)], ['54', '55'])).
% 4.67/4.92  thf('172', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('173', plain, ((v1_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('174', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         ((k10_relat_1 @ sk_B @ 
% 4.67/4.92           (k6_subset_1 @ X1 @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))))
% 4.67/4.92           = (k10_relat_1 @ sk_B @ X1))),
% 4.67/4.92      inference('demod', [status(thm)], ['170', '171', '172', '173'])).
% 4.67/4.92  thf('175', plain,
% 4.67/4.92      (![X28 : $i, X29 : $i]:
% 4.67/4.92         ((r1_tarski @ (k10_relat_1 @ X28 @ X29) @ (k1_relat_1 @ X28))
% 4.67/4.92          | ~ (v1_relat_1 @ X28))),
% 4.67/4.92      inference('cnf', [status(esa)], [t167_relat_1])).
% 4.67/4.92  thf('176', plain,
% 4.67/4.92      (![X12 : $i, X14 : $i]:
% 4.67/4.92         (((X12) = (X14))
% 4.67/4.92          | ~ (r1_tarski @ X14 @ X12)
% 4.67/4.92          | ~ (r1_tarski @ X12 @ X14))),
% 4.67/4.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.67/4.92  thf('177', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         (~ (v1_relat_1 @ X0)
% 4.67/4.92          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 4.67/4.92          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 4.67/4.92      inference('sup-', [status(thm)], ['175', '176'])).
% 4.67/4.92  thf('178', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 4.67/4.92          | ((k1_relat_1 @ sk_B)
% 4.67/4.92              = (k10_relat_1 @ sk_B @ 
% 4.67/4.92                 (k6_subset_1 @ X0 @ (k6_subset_1 @ X1 @ (k2_relat_1 @ sk_B)))))
% 4.67/4.92          | ~ (v1_relat_1 @ sk_B))),
% 4.67/4.92      inference('sup-', [status(thm)], ['174', '177'])).
% 4.67/4.92  thf('179', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         ((k10_relat_1 @ sk_B @ 
% 4.67/4.92           (k6_subset_1 @ X1 @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))))
% 4.67/4.92           = (k10_relat_1 @ sk_B @ X1))),
% 4.67/4.92      inference('demod', [status(thm)], ['170', '171', '172', '173'])).
% 4.67/4.92  thf('180', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('181', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 4.67/4.92          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 4.67/4.92      inference('demod', [status(thm)], ['178', '179', '180'])).
% 4.67/4.92  thf('182', plain,
% 4.67/4.92      ((~ (v1_relat_1 @ sk_B)
% 4.67/4.92        | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 4.67/4.92      inference('sup-', [status(thm)], ['29', '181'])).
% 4.67/4.92  thf('183', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('184', plain,
% 4.67/4.92      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 4.67/4.92      inference('demod', [status(thm)], ['182', '183'])).
% 4.67/4.92  thf('185', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         (~ (v1_funct_1 @ X0)
% 4.67/4.92          | ~ (v1_relat_1 @ X0)
% 4.67/4.92          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 4.67/4.92              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 4.67/4.92      inference('simplify', [status(thm)], ['72'])).
% 4.67/4.92  thf('186', plain,
% 4.67/4.92      ((((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))
% 4.67/4.92          = (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B)))
% 4.67/4.92        | ~ (v1_relat_1 @ sk_B)
% 4.67/4.92        | ~ (v1_funct_1 @ sk_B))),
% 4.67/4.92      inference('sup+', [status(thm)], ['184', '185'])).
% 4.67/4.92  thf('187', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 4.67/4.92      inference('demod', [status(thm)], ['58', '65'])).
% 4.67/4.92  thf('188', plain,
% 4.67/4.92      (![X18 : $i, X19 : $i]:
% 4.67/4.92         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 4.67/4.92           = (k3_xboole_0 @ X18 @ X19))),
% 4.67/4.92      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.67/4.92  thf('189', plain,
% 4.67/4.92      (![X0 : $i]: ((k6_subset_1 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 4.67/4.92      inference('sup+', [status(thm)], ['187', '188'])).
% 4.67/4.92  thf('190', plain, (![X16 : $i]: ((k6_subset_1 @ X16 @ k1_xboole_0) = (X16))),
% 4.67/4.92      inference('demod', [status(thm)], ['54', '55'])).
% 4.67/4.92  thf('191', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.67/4.92      inference('demod', [status(thm)], ['189', '190'])).
% 4.67/4.92  thf('192', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('193', plain, ((v1_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('194', plain,
% 4.67/4.92      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 4.67/4.92      inference('demod', [status(thm)], ['186', '191', '192', '193'])).
% 4.67/4.92  thf('195', plain,
% 4.67/4.92      (![X42 : $i, X43 : $i]:
% 4.67/4.92         (((k9_relat_1 @ X43 @ (k10_relat_1 @ X43 @ X42))
% 4.67/4.92            = (k3_xboole_0 @ X42 @ (k9_relat_1 @ X43 @ (k1_relat_1 @ X43))))
% 4.67/4.92          | ~ (v1_funct_1 @ X43)
% 4.67/4.92          | ~ (v1_relat_1 @ X43))),
% 4.67/4.92      inference('cnf', [status(esa)], [t148_funct_1])).
% 4.67/4.92  thf('196', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 4.67/4.92            = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 4.67/4.92          | ~ (v1_relat_1 @ sk_B)
% 4.67/4.92          | ~ (v1_funct_1 @ sk_B))),
% 4.67/4.92      inference('sup+', [status(thm)], ['194', '195'])).
% 4.67/4.92  thf('197', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('198', plain, ((v1_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('199', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 4.67/4.92           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 4.67/4.92      inference('demod', [status(thm)], ['196', '197', '198'])).
% 4.67/4.92  thf('200', plain,
% 4.67/4.92      (![X44 : $i, X45 : $i, X46 : $i]:
% 4.67/4.92         ((r1_tarski @ X44 @ X45)
% 4.67/4.92          | ~ (v1_relat_1 @ X46)
% 4.67/4.92          | ~ (v1_funct_1 @ X46)
% 4.67/4.92          | ~ (v2_funct_1 @ X46)
% 4.67/4.92          | ~ (r1_tarski @ X44 @ (k1_relat_1 @ X46))
% 4.67/4.92          | ~ (r1_tarski @ (k9_relat_1 @ X46 @ X44) @ (k9_relat_1 @ X46 @ X45)))),
% 4.67/4.92      inference('cnf', [status(esa)], [t157_funct_1])).
% 4.67/4.92  thf('201', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 4.67/4.92             (k9_relat_1 @ sk_B @ X1))
% 4.67/4.92          | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 4.67/4.92          | ~ (v2_funct_1 @ sk_B)
% 4.67/4.92          | ~ (v1_funct_1 @ sk_B)
% 4.67/4.92          | ~ (v1_relat_1 @ sk_B)
% 4.67/4.92          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1))),
% 4.67/4.92      inference('sup-', [status(thm)], ['199', '200'])).
% 4.67/4.92  thf('202', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         ((k10_relat_1 @ sk_B @ 
% 4.67/4.92           (k6_subset_1 @ X1 @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))))
% 4.67/4.92           = (k10_relat_1 @ sk_B @ X1))),
% 4.67/4.92      inference('demod', [status(thm)], ['170', '171', '172', '173'])).
% 4.67/4.92  thf('203', plain,
% 4.67/4.92      (![X28 : $i, X29 : $i]:
% 4.67/4.92         ((r1_tarski @ (k10_relat_1 @ X28 @ X29) @ (k1_relat_1 @ X28))
% 4.67/4.92          | ~ (v1_relat_1 @ X28))),
% 4.67/4.92      inference('cnf', [status(esa)], [t167_relat_1])).
% 4.67/4.92  thf('204', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 4.67/4.92          | ~ (v1_relat_1 @ sk_B))),
% 4.67/4.92      inference('sup+', [status(thm)], ['202', '203'])).
% 4.67/4.92  thf('205', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('206', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 4.67/4.92      inference('demod', [status(thm)], ['204', '205'])).
% 4.67/4.92  thf('207', plain, ((v2_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('208', plain, ((v1_funct_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('209', plain, ((v1_relat_1 @ sk_B)),
% 4.67/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.92  thf('210', plain,
% 4.67/4.92      (![X0 : $i, X1 : $i]:
% 4.67/4.92         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 4.67/4.92             (k9_relat_1 @ sk_B @ X1))
% 4.67/4.92          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1))),
% 4.67/4.92      inference('demod', [status(thm)], ['201', '206', '207', '208', '209'])).
% 4.67/4.92  thf('211', plain,
% 4.67/4.92      (![X0 : $i]:
% 4.67/4.92         (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) @ X0)),
% 4.67/4.92      inference('sup-', [status(thm)], ['22', '210'])).
% 4.67/4.92  thf('212', plain, ($false), inference('demod', [status(thm)], ['8', '211'])).
% 4.67/4.92  
% 4.67/4.92  % SZS output end Refutation
% 4.67/4.92  
% 4.67/4.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
