%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UEAWB0X7ei

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:35 EST 2020

% Result     : Theorem 3.57s
% Output     : Refutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 104 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   17
%              Number of atoms          :  882 (1219 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   14 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) @ X18 )
        = ( k3_xboole_0 @ X16 @ ( k10_relat_1 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) @ X18 )
        = ( k3_xboole_0 @ X16 @ ( k10_relat_1 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(t101_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ B @ A ) @ A )
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) @ X9 )
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t101_relat_1])).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) @ X18 )
        = ( k3_xboole_0 @ X16 @ ( k10_relat_1 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) @ X7 )
        = ( k7_relat_1 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) @ X18 )
        = ( k3_xboole_0 @ X16 @ ( k10_relat_1 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X19 @ ( k10_relat_1 @ X19 @ X20 ) ) @ X20 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X10 @ X11 ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','47'])).

thf(t149_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t149_funct_1])).

thf('49',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['52','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UEAWB0X7ei
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:47:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 3.57/3.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.57/3.82  % Solved by: fo/fo7.sh
% 3.57/3.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.57/3.82  % done 1685 iterations in 3.365s
% 3.57/3.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.57/3.82  % SZS output start Refutation
% 3.57/3.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.57/3.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.57/3.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.57/3.82  thf(sk_C_type, type, sk_C: $i).
% 3.57/3.82  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.57/3.82  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.57/3.82  thf(sk_A_type, type, sk_A: $i).
% 3.57/3.82  thf(sk_B_type, type, sk_B: $i).
% 3.57/3.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.57/3.82  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.57/3.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.57/3.82  thf(commutativity_k3_xboole_0, axiom,
% 3.57/3.82    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.57/3.82  thf('0', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.57/3.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.57/3.82  thf(t139_funct_1, axiom,
% 3.57/3.82    (![A:$i,B:$i,C:$i]:
% 3.57/3.82     ( ( v1_relat_1 @ C ) =>
% 3.57/3.82       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 3.57/3.82         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 3.57/3.82  thf('1', plain,
% 3.57/3.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.57/3.82         (((k10_relat_1 @ (k7_relat_1 @ X17 @ X16) @ X18)
% 3.57/3.82            = (k3_xboole_0 @ X16 @ (k10_relat_1 @ X17 @ X18)))
% 3.57/3.82          | ~ (v1_relat_1 @ X17))),
% 3.57/3.82      inference('cnf', [status(esa)], [t139_funct_1])).
% 3.57/3.82  thf('2', plain,
% 3.57/3.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.57/3.82         (((k10_relat_1 @ (k7_relat_1 @ X17 @ X16) @ X18)
% 3.57/3.82            = (k3_xboole_0 @ X16 @ (k10_relat_1 @ X17 @ X18)))
% 3.57/3.82          | ~ (v1_relat_1 @ X17))),
% 3.57/3.82      inference('cnf', [status(esa)], [t139_funct_1])).
% 3.57/3.82  thf(fc8_funct_1, axiom,
% 3.57/3.82    (![A:$i,B:$i]:
% 3.57/3.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.57/3.82       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 3.57/3.82         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 3.57/3.82  thf('3', plain,
% 3.57/3.82      (![X14 : $i, X15 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X14)
% 3.57/3.82          | ~ (v1_relat_1 @ X14)
% 3.57/3.82          | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 3.57/3.82      inference('cnf', [status(esa)], [fc8_funct_1])).
% 3.57/3.82  thf(t101_relat_1, axiom,
% 3.57/3.82    (![A:$i,B:$i]:
% 3.57/3.82     ( ( v1_relat_1 @ B ) =>
% 3.57/3.82       ( ( k7_relat_1 @ ( k7_relat_1 @ B @ A ) @ A ) = ( k7_relat_1 @ B @ A ) ) ))).
% 3.57/3.82  thf('4', plain,
% 3.57/3.82      (![X8 : $i, X9 : $i]:
% 3.57/3.82         (((k7_relat_1 @ (k7_relat_1 @ X8 @ X9) @ X9) = (k7_relat_1 @ X8 @ X9))
% 3.57/3.82          | ~ (v1_relat_1 @ X8))),
% 3.57/3.82      inference('cnf', [status(esa)], [t101_relat_1])).
% 3.57/3.82  thf('5', plain,
% 3.57/3.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.57/3.82         (((k10_relat_1 @ (k7_relat_1 @ X17 @ X16) @ X18)
% 3.57/3.82            = (k3_xboole_0 @ X16 @ (k10_relat_1 @ X17 @ X18)))
% 3.57/3.82          | ~ (v1_relat_1 @ X17))),
% 3.57/3.82      inference('cnf', [status(esa)], [t139_funct_1])).
% 3.57/3.82  thf('6', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.57/3.82            = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.57/3.82      inference('sup+', [status(thm)], ['4', '5'])).
% 3.57/3.82  thf('7', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.57/3.82              = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))))),
% 3.57/3.82      inference('sup-', [status(thm)], ['3', '6'])).
% 3.57/3.82  thf('8', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.57/3.82            = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1))),
% 3.57/3.82      inference('simplify', [status(thm)], ['7'])).
% 3.57/3.82  thf('9', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)
% 3.57/3.82            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))))
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1))),
% 3.57/3.82      inference('sup+', [status(thm)], ['2', '8'])).
% 3.57/3.82  thf('10', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)
% 3.57/3.82              = (k3_xboole_0 @ X2 @ 
% 3.57/3.82                 (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))))),
% 3.57/3.82      inference('simplify', [status(thm)], ['9'])).
% 3.57/3.82  thf(t148_relat_1, axiom,
% 3.57/3.82    (![A:$i,B:$i]:
% 3.57/3.82     ( ( v1_relat_1 @ B ) =>
% 3.57/3.82       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.57/3.82  thf('11', plain,
% 3.57/3.82      (![X12 : $i, X13 : $i]:
% 3.57/3.82         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 3.57/3.82          | ~ (v1_relat_1 @ X12))),
% 3.57/3.82      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.57/3.82  thf('12', plain,
% 3.57/3.82      (![X14 : $i, X15 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X14)
% 3.57/3.82          | ~ (v1_relat_1 @ X14)
% 3.57/3.82          | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 3.57/3.82      inference('cnf', [status(esa)], [fc8_funct_1])).
% 3.57/3.82  thf(t100_relat_1, axiom,
% 3.57/3.82    (![A:$i,B:$i,C:$i]:
% 3.57/3.82     ( ( v1_relat_1 @ C ) =>
% 3.57/3.82       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 3.57/3.82         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 3.57/3.82  thf('13', plain,
% 3.57/3.82      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.57/3.82         (((k7_relat_1 @ (k7_relat_1 @ X5 @ X6) @ X7)
% 3.57/3.82            = (k7_relat_1 @ X5 @ (k3_xboole_0 @ X6 @ X7)))
% 3.57/3.82          | ~ (v1_relat_1 @ X5))),
% 3.57/3.82      inference('cnf', [status(esa)], [t100_relat_1])).
% 3.57/3.82  thf('14', plain,
% 3.57/3.82      (![X12 : $i, X13 : $i]:
% 3.57/3.82         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 3.57/3.82          | ~ (v1_relat_1 @ X12))),
% 3.57/3.82      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.57/3.82  thf('15', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 3.57/3.82            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 3.57/3.82      inference('sup+', [status(thm)], ['13', '14'])).
% 3.57/3.82  thf('16', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)))
% 3.57/3.82              = (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 3.57/3.82      inference('sup-', [status(thm)], ['12', '15'])).
% 3.57/3.82  thf('17', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (((k2_relat_1 @ (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)))
% 3.57/3.82            = (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1))),
% 3.57/3.82      inference('simplify', [status(thm)], ['16'])).
% 3.57/3.82  thf('18', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.57/3.82            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | ~ (v1_funct_1 @ X2))),
% 3.57/3.82      inference('sup+', [status(thm)], ['11', '17'])).
% 3.57/3.82  thf('19', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X2)
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | ((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.57/3.82              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 3.57/3.82      inference('simplify', [status(thm)], ['18'])).
% 3.57/3.82  thf('20', plain,
% 3.57/3.82      (![X14 : $i, X15 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X14)
% 3.57/3.82          | ~ (v1_relat_1 @ X14)
% 3.57/3.82          | (v1_funct_1 @ (k7_relat_1 @ X14 @ X15)))),
% 3.57/3.82      inference('cnf', [status(esa)], [fc8_funct_1])).
% 3.57/3.82  thf('21', plain,
% 3.57/3.82      (![X14 : $i, X15 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X14)
% 3.57/3.82          | ~ (v1_relat_1 @ X14)
% 3.57/3.82          | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 3.57/3.82      inference('cnf', [status(esa)], [fc8_funct_1])).
% 3.57/3.82  thf('22', plain,
% 3.57/3.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.57/3.82         (((k10_relat_1 @ (k7_relat_1 @ X17 @ X16) @ X18)
% 3.57/3.82            = (k3_xboole_0 @ X16 @ (k10_relat_1 @ X17 @ X18)))
% 3.57/3.82          | ~ (v1_relat_1 @ X17))),
% 3.57/3.82      inference('cnf', [status(esa)], [t139_funct_1])).
% 3.57/3.82  thf(t145_funct_1, axiom,
% 3.57/3.82    (![A:$i,B:$i]:
% 3.57/3.82     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.57/3.82       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 3.57/3.82  thf('23', plain,
% 3.57/3.82      (![X19 : $i, X20 : $i]:
% 3.57/3.82         ((r1_tarski @ (k9_relat_1 @ X19 @ (k10_relat_1 @ X19 @ X20)) @ X20)
% 3.57/3.82          | ~ (v1_funct_1 @ X19)
% 3.57/3.82          | ~ (v1_relat_1 @ X19))),
% 3.57/3.82      inference('cnf', [status(esa)], [t145_funct_1])).
% 3.57/3.82  thf('24', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ 
% 3.57/3.82           (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 3.57/3.82            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 3.57/3.82           X0)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2))
% 3.57/3.82          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X2)))),
% 3.57/3.82      inference('sup+', [status(thm)], ['22', '23'])).
% 3.57/3.82  thf('25', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | (r1_tarski @ 
% 3.57/3.82             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.57/3.82              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 3.57/3.82             X2))),
% 3.57/3.82      inference('sup-', [status(thm)], ['21', '24'])).
% 3.57/3.82  thf('26', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ 
% 3.57/3.82           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.57/3.82            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 3.57/3.82           X2)
% 3.57/3.82          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1))),
% 3.57/3.82      inference('simplify', [status(thm)], ['25'])).
% 3.57/3.82  thf('27', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | (r1_tarski @ 
% 3.57/3.82             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.57/3.82              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 3.57/3.82             X2))),
% 3.57/3.82      inference('sup-', [status(thm)], ['20', '26'])).
% 3.57/3.82  thf('28', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ 
% 3.57/3.82           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.57/3.82            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 3.57/3.82           X2)
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1))),
% 3.57/3.82      inference('simplify', [status(thm)], ['27'])).
% 3.57/3.82  thf('29', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ 
% 3.57/3.82           (k9_relat_1 @ X1 @ 
% 3.57/3.82            (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 3.57/3.82           X0)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1))),
% 3.57/3.82      inference('sup+', [status(thm)], ['19', '28'])).
% 3.57/3.82  thf('30', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | (r1_tarski @ 
% 3.57/3.82             (k9_relat_1 @ X1 @ 
% 3.57/3.82              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 3.57/3.82             X0))),
% 3.57/3.82      inference('simplify', [status(thm)], ['29'])).
% 3.57/3.82  thf('31', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ 
% 3.57/3.82           (k9_relat_1 @ X2 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ X0)
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | ~ (v1_funct_1 @ X2)
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | ~ (v1_funct_1 @ X2))),
% 3.57/3.82      inference('sup+', [status(thm)], ['10', '30'])).
% 3.57/3.82  thf('32', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X2)
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | (r1_tarski @ 
% 3.57/3.82             (k9_relat_1 @ X2 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 3.57/3.82             X0))),
% 3.57/3.82      inference('simplify', [status(thm)], ['31'])).
% 3.57/3.82  thf('33', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ 
% 3.57/3.82           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 3.57/3.82           X0)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1))),
% 3.57/3.82      inference('sup+', [status(thm)], ['1', '32'])).
% 3.57/3.82  thf('34', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | (r1_tarski @ 
% 3.57/3.82             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 3.57/3.82             X0))),
% 3.57/3.82      inference('simplify', [status(thm)], ['33'])).
% 3.57/3.82  thf('35', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X2)
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | ((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.57/3.82              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 3.57/3.82      inference('simplify', [status(thm)], ['18'])).
% 3.57/3.82  thf('36', plain,
% 3.57/3.82      (![X14 : $i, X15 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X14)
% 3.57/3.82          | ~ (v1_relat_1 @ X14)
% 3.57/3.82          | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 3.57/3.82      inference('cnf', [status(esa)], [fc8_funct_1])).
% 3.57/3.82  thf('37', plain,
% 3.57/3.82      (![X12 : $i, X13 : $i]:
% 3.57/3.82         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 3.57/3.82          | ~ (v1_relat_1 @ X12))),
% 3.57/3.82      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.57/3.82  thf(t144_relat_1, axiom,
% 3.57/3.82    (![A:$i,B:$i]:
% 3.57/3.82     ( ( v1_relat_1 @ B ) =>
% 3.57/3.82       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 3.57/3.82  thf('38', plain,
% 3.57/3.82      (![X10 : $i, X11 : $i]:
% 3.57/3.82         ((r1_tarski @ (k9_relat_1 @ X10 @ X11) @ (k2_relat_1 @ X10))
% 3.57/3.82          | ~ (v1_relat_1 @ X10))),
% 3.57/3.82      inference('cnf', [status(esa)], [t144_relat_1])).
% 3.57/3.82  thf('39', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 3.57/3.82           (k9_relat_1 @ X1 @ X0))
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.57/3.82      inference('sup+', [status(thm)], ['37', '38'])).
% 3.57/3.82  thf('40', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 3.57/3.82             (k9_relat_1 @ X1 @ X0)))),
% 3.57/3.82      inference('sup-', [status(thm)], ['36', '39'])).
% 3.57/3.82  thf('41', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 3.57/3.82           (k9_relat_1 @ X1 @ X0))
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1))),
% 3.57/3.82      inference('simplify', [status(thm)], ['40'])).
% 3.57/3.82  thf('42', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.57/3.82           (k9_relat_1 @ X2 @ X1))
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | ~ (v1_funct_1 @ X2)
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | ~ (v1_funct_1 @ X2))),
% 3.57/3.82      inference('sup+', [status(thm)], ['35', '41'])).
% 3.57/3.82  thf('43', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_funct_1 @ X2)
% 3.57/3.82          | ~ (v1_relat_1 @ X2)
% 3.57/3.82          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.57/3.82             (k9_relat_1 @ X2 @ X1)))),
% 3.57/3.82      inference('simplify', [status(thm)], ['42'])).
% 3.57/3.82  thf(t19_xboole_1, axiom,
% 3.57/3.82    (![A:$i,B:$i,C:$i]:
% 3.57/3.82     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 3.57/3.82       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 3.57/3.82  thf('44', plain,
% 3.57/3.82      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.57/3.82         (~ (r1_tarski @ X2 @ X3)
% 3.57/3.82          | ~ (r1_tarski @ X2 @ X4)
% 3.57/3.82          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.57/3.82      inference('cnf', [status(esa)], [t19_xboole_1])).
% 3.57/3.82  thf('45', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.57/3.82         (~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 3.57/3.82             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 3.57/3.82          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 3.57/3.82      inference('sup-', [status(thm)], ['43', '44'])).
% 3.57/3.82  thf('46', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         (~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | (r1_tarski @ 
% 3.57/3.82             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 3.57/3.82             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1))),
% 3.57/3.82      inference('sup-', [status(thm)], ['34', '45'])).
% 3.57/3.82  thf('47', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ 
% 3.57/3.82           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 3.57/3.82           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 3.57/3.82          | ~ (v1_funct_1 @ X1)
% 3.57/3.82          | ~ (v1_relat_1 @ X1))),
% 3.57/3.82      inference('simplify', [status(thm)], ['46'])).
% 3.57/3.82  thf('48', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.82         ((r1_tarski @ 
% 3.57/3.82           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 3.57/3.82           (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 3.57/3.82          | ~ (v1_relat_1 @ X1)
% 3.57/3.82          | ~ (v1_funct_1 @ X1))),
% 3.57/3.82      inference('sup+', [status(thm)], ['0', '47'])).
% 3.57/3.82  thf(t149_funct_1, conjecture,
% 3.57/3.82    (![A:$i,B:$i,C:$i]:
% 3.57/3.82     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.57/3.82       ( r1_tarski @
% 3.57/3.82         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 3.57/3.82         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 3.57/3.82  thf(zf_stmt_0, negated_conjecture,
% 3.57/3.82    (~( ![A:$i,B:$i,C:$i]:
% 3.57/3.82        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.57/3.82          ( r1_tarski @
% 3.57/3.82            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 3.57/3.82            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 3.57/3.82    inference('cnf.neg', [status(esa)], [t149_funct_1])).
% 3.57/3.82  thf('49', plain,
% 3.57/3.82      (~ (r1_tarski @ 
% 3.57/3.82          (k9_relat_1 @ sk_C @ 
% 3.57/3.82           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 3.57/3.82          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 3.57/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.57/3.82  thf('50', plain,
% 3.57/3.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.57/3.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.57/3.82  thf('51', plain,
% 3.57/3.82      (~ (r1_tarski @ 
% 3.57/3.82          (k9_relat_1 @ sk_C @ 
% 3.57/3.82           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 3.57/3.82          (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))),
% 3.57/3.82      inference('demod', [status(thm)], ['49', '50'])).
% 3.57/3.82  thf('52', plain, ((~ (v1_funct_1 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 3.57/3.82      inference('sup-', [status(thm)], ['48', '51'])).
% 3.57/3.82  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 3.57/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.57/3.82  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 3.57/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.57/3.82  thf('55', plain, ($false),
% 3.57/3.82      inference('demod', [status(thm)], ['52', '53', '54'])).
% 3.57/3.82  
% 3.57/3.82  % SZS output end Refutation
% 3.57/3.82  
% 3.57/3.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
