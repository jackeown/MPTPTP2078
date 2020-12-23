%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.itL7fxZ2mo

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:01 EST 2020

% Result     : Theorem 8.35s
% Output     : Refutation 8.35s
% Verified   : 
% Statistics : Number of formulae       :  181 (2705 expanded)
%              Number of leaves         :   25 ( 949 expanded)
%              Depth                    :   18
%              Number of atoms          : 1732 (25013 expanded)
%              Number of equality atoms :  116 (1563 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('13',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X21 @ X22 )
        = ( k7_relat_1 @ X21 @ ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('20',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('21',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('26',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X29 ) @ X28 ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('45',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','52'])).

thf('54',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','43','56'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('59',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('66',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','43','56'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('73',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('76',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('79',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','84'])).

thf('86',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('87',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['85','91'])).

thf('93',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('94',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','84'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('98',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('102',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('103',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','84'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['95','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','104','105'])).

thf('111',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','84'])).

thf('113',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('114',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('121',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['112','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','84'])).

thf('125',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110','129'])).

thf('131',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110','129'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('136',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','134','149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('153',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','151','152'])).

thf('154',plain,(
    $false ),
    inference(simplify,[status(thm)],['153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.itL7fxZ2mo
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:16:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 8.35/8.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.35/8.57  % Solved by: fo/fo7.sh
% 8.35/8.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.35/8.57  % done 7075 iterations in 8.170s
% 8.35/8.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.35/8.57  % SZS output start Refutation
% 8.35/8.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.35/8.57  thf(sk_A_type, type, sk_A: $i).
% 8.35/8.57  thf(sk_B_type, type, sk_B: $i).
% 8.35/8.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 8.35/8.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.35/8.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.35/8.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.35/8.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.35/8.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.35/8.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.35/8.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.35/8.57  thf(t94_relat_1, axiom,
% 8.35/8.57    (![A:$i,B:$i]:
% 8.35/8.57     ( ( v1_relat_1 @ B ) =>
% 8.35/8.57       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 8.35/8.57  thf('0', plain,
% 8.35/8.57      (![X33 : $i, X34 : $i]:
% 8.35/8.57         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.35/8.57          | ~ (v1_relat_1 @ X34))),
% 8.35/8.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.35/8.57  thf(t43_funct_1, conjecture,
% 8.35/8.57    (![A:$i,B:$i]:
% 8.35/8.57     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 8.35/8.57       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.35/8.57  thf(zf_stmt_0, negated_conjecture,
% 8.35/8.57    (~( ![A:$i,B:$i]:
% 8.35/8.57        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 8.35/8.57          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 8.35/8.57    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 8.35/8.57  thf('1', plain,
% 8.35/8.57      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 8.35/8.57         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.35/8.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.57  thf('2', plain,
% 8.35/8.57      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.35/8.57          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 8.35/8.57        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 8.35/8.57      inference('sup-', [status(thm)], ['0', '1'])).
% 8.35/8.57  thf(fc3_funct_1, axiom,
% 8.35/8.57    (![A:$i]:
% 8.35/8.57     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 8.35/8.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 8.35/8.57  thf('3', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('4', plain,
% 8.35/8.57      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.35/8.57         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.35/8.57      inference('demod', [status(thm)], ['2', '3'])).
% 8.35/8.57  thf(commutativity_k3_xboole_0, axiom,
% 8.35/8.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 8.35/8.57  thf('5', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.35/8.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.35/8.57  thf(t17_xboole_1, axiom,
% 8.35/8.57    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 8.35/8.57  thf('6', plain,
% 8.35/8.57      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 8.35/8.57      inference('cnf', [status(esa)], [t17_xboole_1])).
% 8.35/8.57  thf('7', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 8.35/8.57      inference('sup+', [status(thm)], ['5', '6'])).
% 8.35/8.57  thf(t28_xboole_1, axiom,
% 8.35/8.57    (![A:$i,B:$i]:
% 8.35/8.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 8.35/8.57  thf('8', plain,
% 8.35/8.57      (![X7 : $i, X8 : $i]:
% 8.35/8.57         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 8.35/8.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 8.35/8.57  thf('9', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 8.35/8.57           = (k3_xboole_0 @ X1 @ X0))),
% 8.35/8.57      inference('sup-', [status(thm)], ['7', '8'])).
% 8.35/8.57  thf('10', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.35/8.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.35/8.57  thf('11', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 8.35/8.57           = (k3_xboole_0 @ X1 @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['9', '10'])).
% 8.35/8.57  thf('12', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.35/8.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.35/8.57  thf(t71_relat_1, axiom,
% 8.35/8.57    (![A:$i]:
% 8.35/8.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.35/8.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.35/8.57  thf('13', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.35/8.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.35/8.57  thf(t192_relat_1, axiom,
% 8.35/8.57    (![A:$i,B:$i]:
% 8.35/8.57     ( ( v1_relat_1 @ B ) =>
% 8.35/8.57       ( ( k7_relat_1 @ B @ A ) =
% 8.35/8.57         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 8.35/8.57  thf('14', plain,
% 8.35/8.57      (![X21 : $i, X22 : $i]:
% 8.35/8.57         (((k7_relat_1 @ X21 @ X22)
% 8.35/8.57            = (k7_relat_1 @ X21 @ (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22)))
% 8.35/8.57          | ~ (v1_relat_1 @ X21))),
% 8.35/8.57      inference('cnf', [status(esa)], [t192_relat_1])).
% 8.35/8.57  thf('15', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.57            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['13', '14'])).
% 8.35/8.57  thf('16', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('17', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.57           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 8.35/8.57      inference('demod', [status(thm)], ['15', '16'])).
% 8.35/8.57  thf('18', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.57           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['12', '17'])).
% 8.35/8.57  thf('19', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 8.35/8.57           = (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.35/8.57              (k3_xboole_0 @ X1 @ X0)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['11', '18'])).
% 8.35/8.57  thf(t80_relat_1, axiom,
% 8.35/8.57    (![A:$i]:
% 8.35/8.57     ( ( v1_relat_1 @ A ) =>
% 8.35/8.57       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 8.35/8.57  thf('20', plain,
% 8.35/8.57      (![X32 : $i]:
% 8.35/8.57         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 8.35/8.57          | ~ (v1_relat_1 @ X32))),
% 8.35/8.57      inference('cnf', [status(esa)], [t80_relat_1])).
% 8.35/8.57  thf('21', plain,
% 8.35/8.57      (![X33 : $i, X34 : $i]:
% 8.35/8.57         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.35/8.57          | ~ (v1_relat_1 @ X34))),
% 8.35/8.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.35/8.57  thf('22', plain,
% 8.35/8.57      (![X0 : $i]:
% 8.35/8.57         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 8.35/8.57            = (k6_relat_1 @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 8.35/8.57      inference('sup+', [status(thm)], ['20', '21'])).
% 8.35/8.57  thf('23', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 8.35/8.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.35/8.57  thf('24', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('25', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 8.35/8.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.35/8.57  thf('26', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('27', plain,
% 8.35/8.57      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 8.35/8.57  thf('28', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 8.35/8.57           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.35/8.57      inference('demod', [status(thm)], ['19', '27'])).
% 8.35/8.57  thf(t100_relat_1, axiom,
% 8.35/8.57    (![A:$i,B:$i,C:$i]:
% 8.35/8.57     ( ( v1_relat_1 @ C ) =>
% 8.35/8.57       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 8.35/8.57         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 8.35/8.57  thf('29', plain,
% 8.35/8.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.35/8.57         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 8.35/8.57            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 8.35/8.57          | ~ (v1_relat_1 @ X18))),
% 8.35/8.57      inference('cnf', [status(esa)], [t100_relat_1])).
% 8.35/8.57  thf('30', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.57           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['12', '17'])).
% 8.35/8.57  thf('31', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.57            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['29', '30'])).
% 8.35/8.57  thf('32', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('33', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.57           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['31', '32'])).
% 8.35/8.57  thf('34', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.57           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['31', '32'])).
% 8.35/8.57  thf('35', plain,
% 8.35/8.57      (![X33 : $i, X34 : $i]:
% 8.35/8.57         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.35/8.57          | ~ (v1_relat_1 @ X34))),
% 8.35/8.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.35/8.57  thf(t76_relat_1, axiom,
% 8.35/8.57    (![A:$i,B:$i]:
% 8.35/8.57     ( ( v1_relat_1 @ B ) =>
% 8.35/8.57       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 8.35/8.57         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 8.35/8.57  thf('36', plain,
% 8.35/8.57      (![X28 : $i, X29 : $i]:
% 8.35/8.57         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X29) @ X28) @ X28)
% 8.35/8.57          | ~ (v1_relat_1 @ X28))),
% 8.35/8.57      inference('cnf', [status(esa)], [t76_relat_1])).
% 8.35/8.57  thf(d10_xboole_0, axiom,
% 8.35/8.57    (![A:$i,B:$i]:
% 8.35/8.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.35/8.57  thf('37', plain,
% 8.35/8.57      (![X2 : $i, X4 : $i]:
% 8.35/8.57         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 8.35/8.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.35/8.57  thf('38', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ X0)
% 8.35/8.57          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.35/8.57          | ((X0) = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.35/8.57      inference('sup-', [status(thm)], ['36', '37'])).
% 8.35/8.57  thf('39', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (~ (r1_tarski @ X1 @ (k7_relat_1 @ X1 @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ X1)
% 8.35/8.57          | ((X1) = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 8.35/8.57          | ~ (v1_relat_1 @ X1))),
% 8.35/8.57      inference('sup-', [status(thm)], ['35', '38'])).
% 8.35/8.57  thf('40', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (((X1) = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 8.35/8.57          | ~ (v1_relat_1 @ X1)
% 8.35/8.57          | ~ (r1_tarski @ X1 @ (k7_relat_1 @ X1 @ X0)))),
% 8.35/8.57      inference('simplify', [status(thm)], ['39'])).
% 8.35/8.57  thf('41', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (~ (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.35/8.57             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.35/8.57          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.35/8.57              = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 8.35/8.57                 (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))))),
% 8.35/8.57      inference('sup-', [status(thm)], ['34', '40'])).
% 8.35/8.57  thf('42', plain,
% 8.35/8.57      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 8.35/8.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.35/8.57  thf('43', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 8.35/8.57      inference('simplify', [status(thm)], ['42'])).
% 8.35/8.57  thf('44', plain,
% 8.35/8.57      (![X33 : $i, X34 : $i]:
% 8.35/8.57         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.35/8.57          | ~ (v1_relat_1 @ X34))),
% 8.35/8.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.35/8.57  thf('45', plain,
% 8.35/8.57      (![X28 : $i, X29 : $i]:
% 8.35/8.57         ((r1_tarski @ (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) @ X28)
% 8.35/8.57          | ~ (v1_relat_1 @ X28))),
% 8.35/8.57      inference('cnf', [status(esa)], [t76_relat_1])).
% 8.35/8.57  thf('46', plain,
% 8.35/8.57      (![X7 : $i, X8 : $i]:
% 8.35/8.57         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 8.35/8.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 8.35/8.57  thf('47', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ X0)
% 8.35/8.57          | ((k3_xboole_0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 8.35/8.57              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 8.35/8.57      inference('sup-', [status(thm)], ['45', '46'])).
% 8.35/8.57  thf('48', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.35/8.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.35/8.57  thf('49', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ X0)
% 8.35/8.57          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 8.35/8.57              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 8.35/8.57      inference('demod', [status(thm)], ['47', '48'])).
% 8.35/8.57  thf(fc1_relat_1, axiom,
% 8.35/8.57    (![A:$i,B:$i]:
% 8.35/8.57     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.35/8.57  thf('50', plain,
% 8.35/8.57      (![X16 : $i, X17 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k3_xboole_0 @ X16 @ X17)))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc1_relat_1])).
% 8.35/8.57  thf('51', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 8.35/8.57          | ~ (v1_relat_1 @ X1)
% 8.35/8.57          | ~ (v1_relat_1 @ X1))),
% 8.35/8.57      inference('sup+', [status(thm)], ['49', '50'])).
% 8.35/8.57  thf('52', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ X1)
% 8.35/8.57          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 8.35/8.57      inference('simplify', [status(thm)], ['51'])).
% 8.35/8.57  thf('53', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['44', '52'])).
% 8.35/8.57  thf('54', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('55', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('56', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['53', '54', '55'])).
% 8.35/8.57  thf('57', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.35/8.57           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 8.35/8.57              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.35/8.57      inference('demod', [status(thm)], ['41', '43', '56'])).
% 8.35/8.57  thf(t55_relat_1, axiom,
% 8.35/8.57    (![A:$i]:
% 8.35/8.57     ( ( v1_relat_1 @ A ) =>
% 8.35/8.57       ( ![B:$i]:
% 8.35/8.57         ( ( v1_relat_1 @ B ) =>
% 8.35/8.57           ( ![C:$i]:
% 8.35/8.57             ( ( v1_relat_1 @ C ) =>
% 8.35/8.57               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 8.35/8.57                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 8.35/8.57  thf('58', plain,
% 8.35/8.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ X23)
% 8.35/8.57          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 8.35/8.57              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 8.35/8.57          | ~ (v1_relat_1 @ X25)
% 8.35/8.57          | ~ (v1_relat_1 @ X24))),
% 8.35/8.57      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.35/8.57  thf('59', plain,
% 8.35/8.57      (![X28 : $i, X29 : $i]:
% 8.35/8.57         ((r1_tarski @ (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) @ X28)
% 8.35/8.57          | ~ (v1_relat_1 @ X28))),
% 8.35/8.57      inference('cnf', [status(esa)], [t76_relat_1])).
% 8.35/8.57  thf('60', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         ((r1_tarski @ 
% 8.35/8.57           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 8.35/8.57           (k5_relat_1 @ X2 @ X1))
% 8.35/8.57          | ~ (v1_relat_1 @ X2)
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ X1)
% 8.35/8.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['58', '59'])).
% 8.35/8.57  thf('61', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('62', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         ((r1_tarski @ 
% 8.35/8.57           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 8.35/8.57           (k5_relat_1 @ X2 @ X1))
% 8.35/8.57          | ~ (v1_relat_1 @ X2)
% 8.35/8.57          | ~ (v1_relat_1 @ X1)
% 8.35/8.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 8.35/8.57      inference('demod', [status(thm)], ['60', '61'])).
% 8.35/8.57  thf('63', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.35/8.57          | (r1_tarski @ 
% 8.35/8.57             (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 8.35/8.57              (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.35/8.57               (k6_relat_1 @ X2))) @ 
% 8.35/8.57             (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 8.35/8.57              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))))),
% 8.35/8.57      inference('sup-', [status(thm)], ['57', '62'])).
% 8.35/8.57  thf('64', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['53', '54', '55'])).
% 8.35/8.57  thf('65', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['53', '54', '55'])).
% 8.35/8.57  thf('66', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('67', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.35/8.57           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 8.35/8.57              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.35/8.57      inference('demod', [status(thm)], ['41', '43', '56'])).
% 8.35/8.57  thf('68', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         (r1_tarski @ 
% 8.35/8.57          (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 8.35/8.57           (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.35/8.57            (k6_relat_1 @ X2))) @ 
% 8.35/8.57          (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 8.35/8.57  thf('69', plain,
% 8.35/8.57      (![X33 : $i, X34 : $i]:
% 8.35/8.57         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.35/8.57          | ~ (v1_relat_1 @ X34))),
% 8.35/8.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.35/8.57  thf('70', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ X0)
% 8.35/8.57          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 8.35/8.57              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 8.35/8.57      inference('demod', [status(thm)], ['47', '48'])).
% 8.35/8.57  thf('71', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 8.35/8.57            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.35/8.57            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['69', '70'])).
% 8.35/8.57  thf('72', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('73', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('74', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 8.35/8.57           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.35/8.57           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 8.35/8.57      inference('demod', [status(thm)], ['71', '72', '73'])).
% 8.35/8.57  thf('75', plain,
% 8.35/8.57      (![X33 : $i, X34 : $i]:
% 8.35/8.57         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.35/8.57          | ~ (v1_relat_1 @ X34))),
% 8.35/8.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.35/8.57  thf('76', plain,
% 8.35/8.57      (![X28 : $i, X29 : $i]:
% 8.35/8.57         ((r1_tarski @ (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) @ X28)
% 8.35/8.57          | ~ (v1_relat_1 @ X28))),
% 8.35/8.57      inference('cnf', [status(esa)], [t76_relat_1])).
% 8.35/8.57  thf('77', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.35/8.57           (k6_relat_1 @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['75', '76'])).
% 8.35/8.57  thf('78', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('79', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('80', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['77', '78', '79'])).
% 8.35/8.57  thf('81', plain,
% 8.35/8.57      (![X7 : $i, X8 : $i]:
% 8.35/8.57         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 8.35/8.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 8.35/8.57  thf('82', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k3_xboole_0 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.35/8.57           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.35/8.57      inference('sup-', [status(thm)], ['80', '81'])).
% 8.35/8.57  thf('83', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.35/8.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.35/8.57  thf('84', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 8.35/8.57           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.35/8.57           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['82', '83'])).
% 8.35/8.57  thf('85', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 8.35/8.57           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.35/8.57      inference('sup+', [status(thm)], ['74', '84'])).
% 8.35/8.57  thf('86', plain,
% 8.35/8.57      (![X33 : $i, X34 : $i]:
% 8.35/8.57         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.35/8.57          | ~ (v1_relat_1 @ X34))),
% 8.35/8.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.35/8.57  thf('87', plain,
% 8.35/8.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ X23)
% 8.35/8.57          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 8.35/8.57              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 8.35/8.57          | ~ (v1_relat_1 @ X25)
% 8.35/8.57          | ~ (v1_relat_1 @ X24))),
% 8.35/8.57      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.35/8.57  thf('88', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.35/8.57            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 8.35/8.57          | ~ (v1_relat_1 @ X1)
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ X2)
% 8.35/8.57          | ~ (v1_relat_1 @ X1))),
% 8.35/8.57      inference('sup+', [status(thm)], ['86', '87'])).
% 8.35/8.57  thf('89', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('90', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.35/8.57            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 8.35/8.57          | ~ (v1_relat_1 @ X1)
% 8.35/8.57          | ~ (v1_relat_1 @ X2)
% 8.35/8.57          | ~ (v1_relat_1 @ X1))),
% 8.35/8.57      inference('demod', [status(thm)], ['88', '89'])).
% 8.35/8.57  thf('91', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ X2)
% 8.35/8.57          | ~ (v1_relat_1 @ X1)
% 8.35/8.57          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.35/8.57              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.35/8.57      inference('simplify', [status(thm)], ['90'])).
% 8.35/8.57  thf('92', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 8.35/8.57            (k6_relat_1 @ X1))
% 8.35/8.57            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.35/8.57               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['85', '91'])).
% 8.35/8.57  thf('93', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('94', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('95', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 8.35/8.57           (k6_relat_1 @ X1))
% 8.35/8.57           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.35/8.57              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.35/8.57      inference('demod', [status(thm)], ['92', '93', '94'])).
% 8.35/8.57  thf('96', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 8.35/8.57           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.35/8.57      inference('sup+', [status(thm)], ['74', '84'])).
% 8.35/8.57  thf('97', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ X2)
% 8.35/8.57          | ~ (v1_relat_1 @ X1)
% 8.35/8.57          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.35/8.57              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.35/8.57      inference('simplify', [status(thm)], ['90'])).
% 8.35/8.57  thf('98', plain,
% 8.35/8.57      (![X33 : $i, X34 : $i]:
% 8.35/8.57         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.35/8.57          | ~ (v1_relat_1 @ X34))),
% 8.35/8.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.35/8.57  thf('99', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 8.35/8.57            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ X2)
% 8.35/8.57          | ~ (v1_relat_1 @ X0)
% 8.35/8.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 8.35/8.57      inference('sup+', [status(thm)], ['97', '98'])).
% 8.35/8.57  thf('100', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.35/8.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.35/8.57          | ((k7_relat_1 @ 
% 8.35/8.57              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)) @ X2)
% 8.35/8.57              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 8.35/8.57                 (k6_relat_1 @ X1))))),
% 8.35/8.57      inference('sup-', [status(thm)], ['96', '99'])).
% 8.35/8.57  thf('101', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.35/8.57      inference('demod', [status(thm)], ['53', '54', '55'])).
% 8.35/8.57  thf('102', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('103', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.57  thf('104', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i]:
% 8.35/8.57         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 8.35/8.57           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.35/8.57      inference('sup+', [status(thm)], ['74', '84'])).
% 8.35/8.57  thf('105', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 8.35/8.57           (k6_relat_1 @ X1))
% 8.35/8.57           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.35/8.57              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.35/8.57      inference('demod', [status(thm)], ['92', '93', '94'])).
% 8.35/8.57  thf('106', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 8.35/8.57           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.35/8.57              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.35/8.57      inference('demod', [status(thm)],
% 8.35/8.57                ['100', '101', '102', '103', '104', '105'])).
% 8.35/8.57  thf('107', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 8.35/8.57           (k6_relat_1 @ X1))
% 8.35/8.57           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 8.35/8.57      inference('demod', [status(thm)], ['95', '106'])).
% 8.35/8.57  thf('108', plain,
% 8.35/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.57         (r1_tarski @ 
% 8.35/8.57          (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 8.35/8.57           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0)) @ 
% 8.35/8.58          (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.35/8.58      inference('demod', [status(thm)], ['68', '107'])).
% 8.35/8.58  thf('109', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         (r1_tarski @ 
% 8.35/8.58          (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.35/8.58           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 8.35/8.58          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.35/8.58      inference('sup+', [status(thm)], ['33', '108'])).
% 8.35/8.58  thf('110', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.58         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 8.35/8.58           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.35/8.58              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.35/8.58      inference('demod', [status(thm)],
% 8.35/8.58                ['100', '101', '102', '103', '104', '105'])).
% 8.35/8.58  thf('111', plain,
% 8.35/8.58      (![X33 : $i, X34 : $i]:
% 8.35/8.58         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.35/8.58          | ~ (v1_relat_1 @ X34))),
% 8.35/8.58      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.35/8.58  thf('112', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 8.35/8.58           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.35/8.58      inference('sup+', [status(thm)], ['74', '84'])).
% 8.35/8.58  thf('113', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 8.35/8.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.35/8.58  thf('114', plain,
% 8.35/8.58      (![X32 : $i]:
% 8.35/8.58         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 8.35/8.58          | ~ (v1_relat_1 @ X32))),
% 8.35/8.58      inference('cnf', [status(esa)], [t80_relat_1])).
% 8.35/8.58  thf('115', plain,
% 8.35/8.58      (![X0 : $i]:
% 8.35/8.58         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 8.35/8.58            = (k6_relat_1 @ X0))
% 8.35/8.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.35/8.58      inference('sup+', [status(thm)], ['113', '114'])).
% 8.35/8.58  thf('116', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.58  thf('117', plain,
% 8.35/8.58      (![X0 : $i]:
% 8.35/8.58         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 8.35/8.58           = (k6_relat_1 @ X0))),
% 8.35/8.58      inference('demod', [status(thm)], ['115', '116'])).
% 8.35/8.58  thf('118', plain,
% 8.35/8.58      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.35/8.58         (~ (v1_relat_1 @ X23)
% 8.35/8.58          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 8.35/8.58              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 8.35/8.58          | ~ (v1_relat_1 @ X25)
% 8.35/8.58          | ~ (v1_relat_1 @ X24))),
% 8.35/8.58      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.35/8.58  thf('119', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.58            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.35/8.58               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 8.35/8.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.35/8.58          | ~ (v1_relat_1 @ X1)
% 8.35/8.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.35/8.58      inference('sup+', [status(thm)], ['117', '118'])).
% 8.35/8.58  thf('120', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.58  thf('121', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.58  thf('122', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.58            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.35/8.58               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 8.35/8.58          | ~ (v1_relat_1 @ X1))),
% 8.35/8.58      inference('demod', [status(thm)], ['119', '120', '121'])).
% 8.35/8.58  thf('123', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.35/8.58            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.35/8.58               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 8.35/8.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.35/8.58      inference('sup+', [status(thm)], ['112', '122'])).
% 8.35/8.58  thf('124', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 8.35/8.58           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.35/8.58      inference('sup+', [status(thm)], ['74', '84'])).
% 8.35/8.58  thf('125', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.58  thf('126', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.35/8.58           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.35/8.58              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.35/8.58      inference('demod', [status(thm)], ['123', '124', '125'])).
% 8.35/8.58  thf('127', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.35/8.58            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))
% 8.35/8.58          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.35/8.58      inference('sup+', [status(thm)], ['111', '126'])).
% 8.35/8.58  thf('128', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.35/8.58      inference('demod', [status(thm)], ['53', '54', '55'])).
% 8.35/8.58  thf('129', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.35/8.58           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 8.35/8.58      inference('demod', [status(thm)], ['127', '128'])).
% 8.35/8.58  thf('130', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.35/8.58          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.35/8.58      inference('demod', [status(thm)], ['109', '110', '129'])).
% 8.35/8.58  thf('131', plain,
% 8.35/8.58      (![X2 : $i, X4 : $i]:
% 8.35/8.58         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 8.35/8.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.35/8.58  thf('132', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         (~ (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.35/8.58             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 8.35/8.58          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.35/8.58              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 8.35/8.58      inference('sup-', [status(thm)], ['130', '131'])).
% 8.35/8.58  thf('133', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.35/8.58          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.35/8.58      inference('demod', [status(thm)], ['109', '110', '129'])).
% 8.35/8.58  thf('134', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.35/8.58           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.35/8.58      inference('demod', [status(thm)], ['132', '133'])).
% 8.35/8.58  thf('135', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.35/8.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.35/8.58  thf('136', plain,
% 8.35/8.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.35/8.58         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 8.35/8.58            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 8.35/8.58          | ~ (v1_relat_1 @ X18))),
% 8.35/8.58      inference('cnf', [status(esa)], [t100_relat_1])).
% 8.35/8.58  thf('137', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.58         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 8.35/8.58            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 8.35/8.58          | ~ (v1_relat_1 @ X2))),
% 8.35/8.58      inference('sup+', [status(thm)], ['135', '136'])).
% 8.35/8.58  thf('138', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.58           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 8.35/8.58      inference('demod', [status(thm)], ['31', '32'])).
% 8.35/8.58  thf('139', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.58         (((k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X0 @ X1))
% 8.35/8.58            = (k7_relat_1 @ 
% 8.35/8.58               (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2))
% 8.35/8.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 8.35/8.58      inference('sup+', [status(thm)], ['137', '138'])).
% 8.35/8.58  thf('140', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.35/8.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.35/8.58  thf('141', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.58         ((k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X0 @ X1))
% 8.35/8.58           = (k7_relat_1 @ 
% 8.35/8.58              (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2))),
% 8.35/8.58      inference('demod', [status(thm)], ['139', '140'])).
% 8.35/8.58  thf('142', plain,
% 8.35/8.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.35/8.58         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 8.35/8.58            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 8.35/8.58          | ~ (v1_relat_1 @ X18))),
% 8.35/8.58      inference('cnf', [status(esa)], [t100_relat_1])).
% 8.35/8.58  thf('143', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.58         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 8.35/8.58            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 8.35/8.58          | ~ (v1_relat_1 @ X2))),
% 8.35/8.58      inference('sup+', [status(thm)], ['135', '136'])).
% 8.35/8.58  thf('144', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.58         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 8.35/8.58            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 8.35/8.58          | ~ (v1_relat_1 @ X2)
% 8.35/8.58          | ~ (v1_relat_1 @ X2))),
% 8.35/8.58      inference('sup+', [status(thm)], ['142', '143'])).
% 8.35/8.58  thf('145', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.58         (~ (v1_relat_1 @ X2)
% 8.35/8.58          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 8.35/8.58              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 8.35/8.58      inference('simplify', [status(thm)], ['144'])).
% 8.35/8.58  thf('146', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.58         (((k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 8.35/8.58            = (k7_relat_1 @ 
% 8.35/8.58               (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X0) @ X2) @ X1))
% 8.35/8.58          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X0)))),
% 8.35/8.58      inference('sup+', [status(thm)], ['141', '145'])).
% 8.35/8.58  thf('147', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.58           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 8.35/8.58      inference('demod', [status(thm)], ['31', '32'])).
% 8.35/8.58  thf('148', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.35/8.58      inference('demod', [status(thm)], ['53', '54', '55'])).
% 8.35/8.58  thf('149', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.58         ((k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 8.35/8.58           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X0) @ X1))),
% 8.35/8.58      inference('demod', [status(thm)], ['146', '147', '148'])).
% 8.35/8.58  thf('150', plain,
% 8.35/8.58      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.35/8.58      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 8.35/8.58  thf('151', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.35/8.58           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.35/8.58      inference('demod', [status(thm)], ['28', '134', '149', '150'])).
% 8.35/8.58  thf('152', plain,
% 8.35/8.58      (![X0 : $i, X1 : $i]:
% 8.35/8.58         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.35/8.58           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.35/8.58      inference('demod', [status(thm)], ['132', '133'])).
% 8.35/8.58  thf('153', plain,
% 8.35/8.58      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.35/8.58         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 8.35/8.58      inference('demod', [status(thm)], ['4', '151', '152'])).
% 8.35/8.58  thf('154', plain, ($false), inference('simplify', [status(thm)], ['153'])).
% 8.35/8.58  
% 8.35/8.58  % SZS output end Refutation
% 8.35/8.58  
% 8.41/8.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
