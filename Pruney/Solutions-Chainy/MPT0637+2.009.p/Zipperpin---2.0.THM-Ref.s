%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RZaLlEcO96

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:56 EST 2020

% Result     : Theorem 14.48s
% Output     : Refutation 14.48s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 533 expanded)
%              Number of leaves         :   29 ( 189 expanded)
%              Depth                    :   17
%              Number of atoms          : 1282 (4687 expanded)
%              Number of equality atoms :   86 ( 354 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X30 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X21 @ X22 )
        = ( k7_relat_1 @ X21 @ ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X29 ) @ X28 ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('41',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','39','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('56',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('68',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('71',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('74',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) ) @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','79'])).

thf('84',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('103',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('104',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('107',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('108',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('109',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','89','102','110'])).

thf('112',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','111'])).

thf('113',plain,(
    $false ),
    inference(simplify,[status(thm)],['112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RZaLlEcO96
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 14.48/14.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.48/14.69  % Solved by: fo/fo7.sh
% 14.48/14.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.48/14.69  % done 7208 iterations in 14.197s
% 14.48/14.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.48/14.69  % SZS output start Refutation
% 14.48/14.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 14.48/14.69  thf(sk_A_type, type, sk_A: $i).
% 14.48/14.69  thf(sk_B_type, type, sk_B: $i).
% 14.48/14.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 14.48/14.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.48/14.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 14.48/14.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 14.48/14.69  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 14.48/14.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.48/14.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.48/14.69  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 14.48/14.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 14.48/14.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 14.48/14.69  thf(t94_relat_1, axiom,
% 14.48/14.69    (![A:$i,B:$i]:
% 14.48/14.69     ( ( v1_relat_1 @ B ) =>
% 14.48/14.69       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 14.48/14.69  thf('0', plain,
% 14.48/14.69      (![X33 : $i, X34 : $i]:
% 14.48/14.69         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 14.48/14.69          | ~ (v1_relat_1 @ X34))),
% 14.48/14.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 14.48/14.69  thf(t43_funct_1, conjecture,
% 14.48/14.69    (![A:$i,B:$i]:
% 14.48/14.69     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 14.48/14.69       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 14.48/14.69  thf(zf_stmt_0, negated_conjecture,
% 14.48/14.69    (~( ![A:$i,B:$i]:
% 14.48/14.69        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 14.48/14.69          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 14.48/14.69    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 14.48/14.69  thf('1', plain,
% 14.48/14.69      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 14.48/14.69         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 14.48/14.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.69  thf('2', plain,
% 14.48/14.69      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 14.48/14.69          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 14.48/14.69        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 14.48/14.69      inference('sup-', [status(thm)], ['0', '1'])).
% 14.48/14.69  thf(fc3_funct_1, axiom,
% 14.48/14.69    (![A:$i]:
% 14.48/14.69     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 14.48/14.69       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 14.48/14.69  thf('3', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('4', plain,
% 14.48/14.69      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 14.48/14.69         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 14.48/14.69      inference('demod', [status(thm)], ['2', '3'])).
% 14.48/14.69  thf('5', plain,
% 14.48/14.69      (![X33 : $i, X34 : $i]:
% 14.48/14.69         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 14.48/14.69          | ~ (v1_relat_1 @ X34))),
% 14.48/14.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 14.48/14.69  thf(t17_xboole_1, axiom,
% 14.48/14.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 14.48/14.69  thf('6', plain,
% 14.48/14.69      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 14.48/14.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 14.48/14.69  thf(t71_relat_1, axiom,
% 14.48/14.69    (![A:$i]:
% 14.48/14.69     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 14.48/14.69       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 14.48/14.69  thf('7', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 14.48/14.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 14.48/14.69  thf(t77_relat_1, axiom,
% 14.48/14.69    (![A:$i,B:$i]:
% 14.48/14.69     ( ( v1_relat_1 @ B ) =>
% 14.48/14.69       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 14.48/14.69         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 14.48/14.69  thf('8', plain,
% 14.48/14.69      (![X30 : $i, X31 : $i]:
% 14.48/14.69         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 14.48/14.69          | ((k5_relat_1 @ (k6_relat_1 @ X31) @ X30) = (X30))
% 14.48/14.69          | ~ (v1_relat_1 @ X30))),
% 14.48/14.69      inference('cnf', [status(esa)], [t77_relat_1])).
% 14.48/14.69  thf('9', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (r1_tarski @ X0 @ X1)
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 14.48/14.69          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 14.48/14.69              = (k6_relat_1 @ X0)))),
% 14.48/14.69      inference('sup-', [status(thm)], ['7', '8'])).
% 14.48/14.69  thf('10', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('11', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (r1_tarski @ X0 @ X1)
% 14.48/14.69          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 14.48/14.69              = (k6_relat_1 @ X0)))),
% 14.48/14.69      inference('demod', [status(thm)], ['9', '10'])).
% 14.48/14.69  thf('12', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 14.48/14.69           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 14.48/14.69           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 14.48/14.69      inference('sup-', [status(thm)], ['6', '11'])).
% 14.48/14.69  thf('13', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 14.48/14.69            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 14.48/14.69      inference('sup+', [status(thm)], ['5', '12'])).
% 14.48/14.69  thf('14', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('15', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 14.48/14.69           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 14.48/14.69      inference('demod', [status(thm)], ['13', '14'])).
% 14.48/14.69  thf('16', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 14.48/14.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 14.48/14.69  thf(t192_relat_1, axiom,
% 14.48/14.69    (![A:$i,B:$i]:
% 14.48/14.69     ( ( v1_relat_1 @ B ) =>
% 14.48/14.69       ( ( k7_relat_1 @ B @ A ) =
% 14.48/14.69         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 14.48/14.69  thf('17', plain,
% 14.48/14.69      (![X21 : $i, X22 : $i]:
% 14.48/14.69         (((k7_relat_1 @ X21 @ X22)
% 14.48/14.69            = (k7_relat_1 @ X21 @ (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22)))
% 14.48/14.69          | ~ (v1_relat_1 @ X21))),
% 14.48/14.69      inference('cnf', [status(esa)], [t192_relat_1])).
% 14.48/14.69  thf('18', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 14.48/14.69            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 14.48/14.69      inference('sup+', [status(thm)], ['16', '17'])).
% 14.48/14.69  thf('19', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('20', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 14.48/14.69           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 14.48/14.69      inference('demod', [status(thm)], ['18', '19'])).
% 14.48/14.69  thf(commutativity_k2_tarski, axiom,
% 14.48/14.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 14.48/14.69  thf('21', plain,
% 14.48/14.69      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 14.48/14.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 14.48/14.69  thf(t12_setfam_1, axiom,
% 14.48/14.69    (![A:$i,B:$i]:
% 14.48/14.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 14.48/14.69  thf('22', plain,
% 14.48/14.69      (![X14 : $i, X15 : $i]:
% 14.48/14.69         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 14.48/14.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 14.48/14.69  thf('23', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 14.48/14.69      inference('sup+', [status(thm)], ['21', '22'])).
% 14.48/14.69  thf('24', plain,
% 14.48/14.69      (![X14 : $i, X15 : $i]:
% 14.48/14.69         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 14.48/14.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 14.48/14.69  thf('25', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.48/14.69      inference('sup+', [status(thm)], ['23', '24'])).
% 14.48/14.69  thf(t100_relat_1, axiom,
% 14.48/14.69    (![A:$i,B:$i,C:$i]:
% 14.48/14.69     ( ( v1_relat_1 @ C ) =>
% 14.48/14.69       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 14.48/14.69         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 14.48/14.69  thf('26', plain,
% 14.48/14.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.69         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 14.48/14.69            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 14.48/14.69          | ~ (v1_relat_1 @ X18))),
% 14.48/14.69      inference('cnf', [status(esa)], [t100_relat_1])).
% 14.48/14.69  thf('27', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 14.48/14.69            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 14.48/14.69          | ~ (v1_relat_1 @ X2))),
% 14.48/14.69      inference('sup+', [status(thm)], ['25', '26'])).
% 14.48/14.69  thf('28', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 14.48/14.69            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 14.48/14.69      inference('sup+', [status(thm)], ['20', '27'])).
% 14.48/14.69  thf('29', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('30', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 14.48/14.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 14.48/14.69      inference('demod', [status(thm)], ['28', '29'])).
% 14.48/14.69  thf('31', plain,
% 14.48/14.69      (![X33 : $i, X34 : $i]:
% 14.48/14.69         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 14.48/14.69          | ~ (v1_relat_1 @ X34))),
% 14.48/14.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 14.48/14.69  thf(t76_relat_1, axiom,
% 14.48/14.69    (![A:$i,B:$i]:
% 14.48/14.69     ( ( v1_relat_1 @ B ) =>
% 14.48/14.69       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 14.48/14.69         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 14.48/14.69  thf('32', plain,
% 14.48/14.69      (![X28 : $i, X29 : $i]:
% 14.48/14.69         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X29) @ X28) @ X28)
% 14.48/14.69          | ~ (v1_relat_1 @ X28))),
% 14.48/14.69      inference('cnf', [status(esa)], [t76_relat_1])).
% 14.48/14.69  thf(d10_xboole_0, axiom,
% 14.48/14.69    (![A:$i,B:$i]:
% 14.48/14.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.48/14.69  thf('33', plain,
% 14.48/14.69      (![X0 : $i, X2 : $i]:
% 14.48/14.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 14.48/14.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.48/14.69  thf('34', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X0)
% 14.48/14.69          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 14.48/14.69          | ((X0) = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 14.48/14.69      inference('sup-', [status(thm)], ['32', '33'])).
% 14.48/14.69  thf('35', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (r1_tarski @ X1 @ (k7_relat_1 @ X1 @ X0))
% 14.48/14.69          | ~ (v1_relat_1 @ X1)
% 14.48/14.69          | ((X1) = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 14.48/14.69          | ~ (v1_relat_1 @ X1))),
% 14.48/14.69      inference('sup-', [status(thm)], ['31', '34'])).
% 14.48/14.69  thf('36', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (((X1) = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 14.48/14.69          | ~ (v1_relat_1 @ X1)
% 14.48/14.69          | ~ (r1_tarski @ X1 @ (k7_relat_1 @ X1 @ X0)))),
% 14.48/14.69      inference('simplify', [status(thm)], ['35'])).
% 14.48/14.69  thf('37', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 14.48/14.69             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 14.48/14.69          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 14.48/14.69          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 14.48/14.69              = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 14.48/14.69                 (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))))),
% 14.48/14.69      inference('sup-', [status(thm)], ['30', '36'])).
% 14.48/14.69  thf('38', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 14.48/14.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.48/14.69  thf('39', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 14.48/14.69      inference('simplify', [status(thm)], ['38'])).
% 14.48/14.69  thf('40', plain,
% 14.48/14.69      (![X33 : $i, X34 : $i]:
% 14.48/14.69         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 14.48/14.69          | ~ (v1_relat_1 @ X34))),
% 14.48/14.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 14.48/14.69  thf('41', plain,
% 14.48/14.69      (![X28 : $i, X29 : $i]:
% 14.48/14.69         ((r1_tarski @ (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) @ X28)
% 14.48/14.69          | ~ (v1_relat_1 @ X28))),
% 14.48/14.69      inference('cnf', [status(esa)], [t76_relat_1])).
% 14.48/14.69  thf(t28_xboole_1, axiom,
% 14.48/14.69    (![A:$i,B:$i]:
% 14.48/14.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 14.48/14.69  thf('42', plain,
% 14.48/14.69      (![X5 : $i, X6 : $i]:
% 14.48/14.69         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 14.48/14.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 14.48/14.69  thf('43', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X0)
% 14.48/14.69          | ((k3_xboole_0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 14.48/14.69              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 14.48/14.69      inference('sup-', [status(thm)], ['41', '42'])).
% 14.48/14.69  thf('44', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.48/14.69      inference('sup+', [status(thm)], ['23', '24'])).
% 14.48/14.69  thf('45', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X0)
% 14.48/14.69          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 14.48/14.69              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 14.48/14.69      inference('demod', [status(thm)], ['43', '44'])).
% 14.48/14.69  thf(fc1_relat_1, axiom,
% 14.48/14.69    (![A:$i,B:$i]:
% 14.48/14.69     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 14.48/14.69  thf('46', plain,
% 14.48/14.69      (![X16 : $i, X17 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k3_xboole_0 @ X16 @ X17)))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc1_relat_1])).
% 14.48/14.69  thf('47', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 14.48/14.69          | ~ (v1_relat_1 @ X1)
% 14.48/14.69          | ~ (v1_relat_1 @ X1))),
% 14.48/14.69      inference('sup+', [status(thm)], ['45', '46'])).
% 14.48/14.69  thf('48', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X1)
% 14.48/14.69          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 14.48/14.69      inference('simplify', [status(thm)], ['47'])).
% 14.48/14.69  thf('49', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 14.48/14.69      inference('sup+', [status(thm)], ['40', '48'])).
% 14.48/14.69  thf('50', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('51', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('52', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 14.48/14.69      inference('demod', [status(thm)], ['49', '50', '51'])).
% 14.48/14.69  thf('53', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 14.48/14.69           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 14.48/14.69              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 14.48/14.69      inference('demod', [status(thm)], ['37', '39', '52'])).
% 14.48/14.69  thf('54', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X1)
% 14.48/14.69          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 14.48/14.69      inference('simplify', [status(thm)], ['47'])).
% 14.48/14.69  thf(t55_relat_1, axiom,
% 14.48/14.69    (![A:$i]:
% 14.48/14.69     ( ( v1_relat_1 @ A ) =>
% 14.48/14.69       ( ![B:$i]:
% 14.48/14.69         ( ( v1_relat_1 @ B ) =>
% 14.48/14.69           ( ![C:$i]:
% 14.48/14.69             ( ( v1_relat_1 @ C ) =>
% 14.48/14.69               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 14.48/14.69                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 14.48/14.69  thf('55', plain,
% 14.48/14.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X23)
% 14.48/14.69          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 14.48/14.69              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 14.48/14.69          | ~ (v1_relat_1 @ X25)
% 14.48/14.69          | ~ (v1_relat_1 @ X24))),
% 14.48/14.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 14.48/14.69  thf('56', plain,
% 14.48/14.69      (![X28 : $i, X29 : $i]:
% 14.48/14.69         ((r1_tarski @ (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) @ X28)
% 14.48/14.69          | ~ (v1_relat_1 @ X28))),
% 14.48/14.69      inference('cnf', [status(esa)], [t76_relat_1])).
% 14.48/14.69  thf('57', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         ((r1_tarski @ 
% 14.48/14.69           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 14.48/14.69           (k5_relat_1 @ X2 @ X1))
% 14.48/14.69          | ~ (v1_relat_1 @ X2)
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 14.48/14.69          | ~ (v1_relat_1 @ X1)
% 14.48/14.69          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 14.48/14.69      inference('sup+', [status(thm)], ['55', '56'])).
% 14.48/14.69  thf('58', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('59', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         ((r1_tarski @ 
% 14.48/14.69           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 14.48/14.69           (k5_relat_1 @ X2 @ X1))
% 14.48/14.69          | ~ (v1_relat_1 @ X2)
% 14.48/14.69          | ~ (v1_relat_1 @ X1)
% 14.48/14.69          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 14.48/14.69      inference('demod', [status(thm)], ['57', '58'])).
% 14.48/14.69  thf('60', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X1)
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 14.48/14.69          | ~ (v1_relat_1 @ X1)
% 14.48/14.69          | (r1_tarski @ 
% 14.48/14.69             (k5_relat_1 @ X1 @ 
% 14.48/14.69              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 14.48/14.69             (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 14.48/14.69      inference('sup-', [status(thm)], ['54', '59'])).
% 14.48/14.69  thf('61', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('62', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X1)
% 14.48/14.69          | ~ (v1_relat_1 @ X1)
% 14.48/14.69          | (r1_tarski @ 
% 14.48/14.69             (k5_relat_1 @ X1 @ 
% 14.48/14.69              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 14.48/14.69             (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 14.48/14.69      inference('demod', [status(thm)], ['60', '61'])).
% 14.48/14.69  thf('63', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         ((r1_tarski @ 
% 14.48/14.69           (k5_relat_1 @ X1 @ 
% 14.48/14.69            (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 14.48/14.69           (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 14.48/14.69          | ~ (v1_relat_1 @ X1))),
% 14.48/14.69      inference('simplify', [status(thm)], ['62'])).
% 14.48/14.69  thf('64', plain,
% 14.48/14.69      (![X33 : $i, X34 : $i]:
% 14.48/14.69         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 14.48/14.69          | ~ (v1_relat_1 @ X34))),
% 14.48/14.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 14.48/14.69  thf('65', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X0)
% 14.48/14.69          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 14.48/14.69              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 14.48/14.69      inference('demod', [status(thm)], ['43', '44'])).
% 14.48/14.69  thf('66', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 14.48/14.69            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 14.48/14.69            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 14.48/14.69      inference('sup+', [status(thm)], ['64', '65'])).
% 14.48/14.69  thf('67', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('68', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('69', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 14.48/14.69           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 14.48/14.69           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 14.48/14.69      inference('demod', [status(thm)], ['66', '67', '68'])).
% 14.48/14.69  thf('70', plain,
% 14.48/14.69      (![X33 : $i, X34 : $i]:
% 14.48/14.69         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 14.48/14.69          | ~ (v1_relat_1 @ X34))),
% 14.48/14.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 14.48/14.69  thf('71', plain,
% 14.48/14.69      (![X28 : $i, X29 : $i]:
% 14.48/14.69         ((r1_tarski @ (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) @ X28)
% 14.48/14.69          | ~ (v1_relat_1 @ X28))),
% 14.48/14.69      inference('cnf', [status(esa)], [t76_relat_1])).
% 14.48/14.69  thf('72', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 14.48/14.69           (k6_relat_1 @ X0))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 14.48/14.69      inference('sup+', [status(thm)], ['70', '71'])).
% 14.48/14.69  thf('73', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('74', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('75', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 14.48/14.69      inference('demod', [status(thm)], ['72', '73', '74'])).
% 14.48/14.69  thf('76', plain,
% 14.48/14.69      (![X5 : $i, X6 : $i]:
% 14.48/14.69         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 14.48/14.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 14.48/14.69  thf('77', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k3_xboole_0 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 14.48/14.69           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 14.48/14.69      inference('sup-', [status(thm)], ['75', '76'])).
% 14.48/14.69  thf('78', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.48/14.69      inference('sup+', [status(thm)], ['23', '24'])).
% 14.48/14.69  thf('79', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 14.48/14.69           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 14.48/14.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 14.48/14.69      inference('demod', [status(thm)], ['77', '78'])).
% 14.48/14.69  thf('80', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 14.48/14.69           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 14.48/14.69      inference('sup+', [status(thm)], ['69', '79'])).
% 14.48/14.69  thf('81', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         ((r1_tarski @ 
% 14.48/14.69           (k5_relat_1 @ X1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X0)) @ 
% 14.48/14.69           (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 14.48/14.69          | ~ (v1_relat_1 @ X1))),
% 14.48/14.69      inference('demod', [status(thm)], ['63', '80'])).
% 14.48/14.69  thf('82', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 14.48/14.69           (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 14.48/14.69      inference('sup+', [status(thm)], ['53', '81'])).
% 14.48/14.69  thf('83', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 14.48/14.69           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 14.48/14.69      inference('sup+', [status(thm)], ['69', '79'])).
% 14.48/14.69  thf('84', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('85', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 14.48/14.69          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 14.48/14.69      inference('demod', [status(thm)], ['82', '83', '84'])).
% 14.48/14.69  thf('86', plain,
% 14.48/14.69      (![X0 : $i, X2 : $i]:
% 14.48/14.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 14.48/14.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.48/14.69  thf('87', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (~ (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 14.48/14.69             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 14.48/14.69          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 14.48/14.69              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 14.48/14.69      inference('sup-', [status(thm)], ['85', '86'])).
% 14.48/14.69  thf('88', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 14.48/14.69          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 14.48/14.69      inference('demod', [status(thm)], ['82', '83', '84'])).
% 14.48/14.69  thf('89', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 14.48/14.69           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 14.48/14.69      inference('demod', [status(thm)], ['87', '88'])).
% 14.48/14.69  thf('90', plain,
% 14.48/14.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.69         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 14.48/14.69            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 14.48/14.69          | ~ (v1_relat_1 @ X18))),
% 14.48/14.69      inference('cnf', [status(esa)], [t100_relat_1])).
% 14.48/14.69  thf('91', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 14.48/14.69            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 14.48/14.69          | ~ (v1_relat_1 @ X2))),
% 14.48/14.69      inference('sup+', [status(thm)], ['25', '26'])).
% 14.48/14.69  thf('92', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 14.48/14.69            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 14.48/14.69          | ~ (v1_relat_1 @ X2)
% 14.48/14.69          | ~ (v1_relat_1 @ X2))),
% 14.48/14.69      inference('sup+', [status(thm)], ['90', '91'])).
% 14.48/14.69  thf('93', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         (~ (v1_relat_1 @ X2)
% 14.48/14.69          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 14.48/14.69              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 14.48/14.69      inference('simplify', [status(thm)], ['92'])).
% 14.48/14.69  thf('94', plain,
% 14.48/14.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.69         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 14.48/14.69            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 14.48/14.69          | ~ (v1_relat_1 @ X18))),
% 14.48/14.69      inference('cnf', [status(esa)], [t100_relat_1])).
% 14.48/14.69  thf('95', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 14.48/14.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 14.48/14.69      inference('demod', [status(thm)], ['28', '29'])).
% 14.48/14.69  thf('96', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         (((k7_relat_1 @ 
% 14.48/14.69            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2)
% 14.48/14.69            = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 14.48/14.69      inference('sup+', [status(thm)], ['94', '95'])).
% 14.48/14.69  thf('97', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('98', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         ((k7_relat_1 @ 
% 14.48/14.69           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2)
% 14.48/14.69           = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 14.48/14.69      inference('demod', [status(thm)], ['96', '97'])).
% 14.48/14.69  thf('99', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         (((k7_relat_1 @ 
% 14.48/14.69            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ X1) @ X0)
% 14.48/14.69            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X2 @ X0)))
% 14.48/14.69          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2)))),
% 14.48/14.69      inference('sup+', [status(thm)], ['93', '98'])).
% 14.48/14.69  thf('100', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 14.48/14.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 14.48/14.69      inference('demod', [status(thm)], ['28', '29'])).
% 14.48/14.69  thf('101', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 14.48/14.69      inference('demod', [status(thm)], ['49', '50', '51'])).
% 14.48/14.69  thf('102', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.69         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ X0)
% 14.48/14.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 14.48/14.69      inference('demod', [status(thm)], ['99', '100', '101'])).
% 14.48/14.69  thf(t80_relat_1, axiom,
% 14.48/14.69    (![A:$i]:
% 14.48/14.69     ( ( v1_relat_1 @ A ) =>
% 14.48/14.69       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 14.48/14.69  thf('103', plain,
% 14.48/14.69      (![X32 : $i]:
% 14.48/14.69         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 14.48/14.69          | ~ (v1_relat_1 @ X32))),
% 14.48/14.69      inference('cnf', [status(esa)], [t80_relat_1])).
% 14.48/14.69  thf('104', plain,
% 14.48/14.69      (![X33 : $i, X34 : $i]:
% 14.48/14.69         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 14.48/14.69          | ~ (v1_relat_1 @ X34))),
% 14.48/14.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 14.48/14.69  thf('105', plain,
% 14.48/14.69      (![X0 : $i]:
% 14.48/14.69         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 14.48/14.69            = (k6_relat_1 @ X0))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 14.48/14.69          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 14.48/14.69      inference('sup+', [status(thm)], ['103', '104'])).
% 14.48/14.69  thf('106', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 14.48/14.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 14.48/14.69  thf('107', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('108', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 14.48/14.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 14.48/14.69  thf('109', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 14.48/14.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 14.48/14.69  thf('110', plain,
% 14.48/14.69      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 14.48/14.69      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 14.48/14.69  thf('111', plain,
% 14.48/14.69      (![X0 : $i, X1 : $i]:
% 14.48/14.69         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 14.48/14.69           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 14.48/14.69      inference('demod', [status(thm)], ['15', '89', '102', '110'])).
% 14.48/14.69  thf('112', plain,
% 14.48/14.69      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 14.48/14.69         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 14.48/14.69      inference('demod', [status(thm)], ['4', '111'])).
% 14.48/14.69  thf('113', plain, ($false), inference('simplify', [status(thm)], ['112'])).
% 14.48/14.69  
% 14.48/14.69  % SZS output end Refutation
% 14.48/14.69  
% 14.48/14.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
