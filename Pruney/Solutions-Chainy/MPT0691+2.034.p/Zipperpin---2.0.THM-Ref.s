%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DkP4LvyBEf

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:22 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 187 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  757 (1622 expanded)
%              Number of equality atoms :   40 (  72 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k10_relat_1 @ X27 @ X25 ) @ ( k10_relat_1 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('20',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X22 @ X23 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('29',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X22 @ X23 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','57','58'])).

thf('60',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DkP4LvyBEf
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:13:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.07/2.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.07/2.26  % Solved by: fo/fo7.sh
% 2.07/2.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.07/2.26  % done 3671 iterations in 1.799s
% 2.07/2.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.07/2.26  % SZS output start Refutation
% 2.07/2.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.07/2.26  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.07/2.26  thf(sk_A_type, type, sk_A: $i).
% 2.07/2.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.07/2.26  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.07/2.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.07/2.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.07/2.26  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.07/2.26  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.07/2.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.07/2.26  thf(sk_B_type, type, sk_B: $i).
% 2.07/2.26  thf(t146_funct_1, conjecture,
% 2.07/2.26    (![A:$i,B:$i]:
% 2.07/2.26     ( ( v1_relat_1 @ B ) =>
% 2.07/2.26       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.07/2.26         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 2.07/2.26  thf(zf_stmt_0, negated_conjecture,
% 2.07/2.26    (~( ![A:$i,B:$i]:
% 2.07/2.26        ( ( v1_relat_1 @ B ) =>
% 2.07/2.26          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.07/2.26            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 2.07/2.26    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 2.07/2.26  thf('0', plain,
% 2.07/2.26      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf(t148_relat_1, axiom,
% 2.07/2.26    (![A:$i,B:$i]:
% 2.07/2.26     ( ( v1_relat_1 @ B ) =>
% 2.07/2.26       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.07/2.26  thf('1', plain,
% 2.07/2.26      (![X20 : $i, X21 : $i]:
% 2.07/2.26         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 2.07/2.26          | ~ (v1_relat_1 @ X20))),
% 2.07/2.26      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.07/2.26  thf(t169_relat_1, axiom,
% 2.07/2.26    (![A:$i]:
% 2.07/2.26     ( ( v1_relat_1 @ A ) =>
% 2.07/2.26       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.07/2.26  thf('2', plain,
% 2.07/2.26      (![X24 : $i]:
% 2.07/2.26         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 2.07/2.26          | ~ (v1_relat_1 @ X24))),
% 2.07/2.26      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.07/2.26  thf('3', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 2.07/2.26            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.07/2.26          | ~ (v1_relat_1 @ X1)
% 2.07/2.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.07/2.26      inference('sup+', [status(thm)], ['1', '2'])).
% 2.07/2.26  thf(dt_k7_relat_1, axiom,
% 2.07/2.26    (![A:$i,B:$i]:
% 2.07/2.26     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.07/2.26  thf('4', plain,
% 2.07/2.26      (![X18 : $i, X19 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 2.07/2.26      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.07/2.26  thf('5', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X1)
% 2.07/2.26          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 2.07/2.26              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.07/2.26      inference('clc', [status(thm)], ['3', '4'])).
% 2.07/2.26  thf('6', plain,
% 2.07/2.26      (![X24 : $i]:
% 2.07/2.26         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 2.07/2.26          | ~ (v1_relat_1 @ X24))),
% 2.07/2.26      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.07/2.26  thf(t7_xboole_1, axiom,
% 2.07/2.26    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.07/2.26  thf('7', plain,
% 2.07/2.26      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 2.07/2.26      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.07/2.26  thf(t178_relat_1, axiom,
% 2.07/2.26    (![A:$i,B:$i,C:$i]:
% 2.07/2.26     ( ( v1_relat_1 @ C ) =>
% 2.07/2.26       ( ( r1_tarski @ A @ B ) =>
% 2.07/2.26         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.07/2.26  thf('8', plain,
% 2.07/2.26      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.07/2.26         (~ (r1_tarski @ X25 @ X26)
% 2.07/2.26          | ~ (v1_relat_1 @ X27)
% 2.07/2.26          | (r1_tarski @ (k10_relat_1 @ X27 @ X25) @ (k10_relat_1 @ X27 @ X26)))),
% 2.07/2.26      inference('cnf', [status(esa)], [t178_relat_1])).
% 2.07/2.26  thf('9', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.07/2.26         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 2.07/2.26           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 2.07/2.26          | ~ (v1_relat_1 @ X2))),
% 2.07/2.26      inference('sup-', [status(thm)], ['7', '8'])).
% 2.07/2.26  thf('10', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.07/2.26           (k10_relat_1 @ X0 @ (k2_xboole_0 @ (k2_relat_1 @ X0) @ X1)))
% 2.07/2.26          | ~ (v1_relat_1 @ X0)
% 2.07/2.26          | ~ (v1_relat_1 @ X0))),
% 2.07/2.26      inference('sup+', [status(thm)], ['6', '9'])).
% 2.07/2.26  thf('11', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X0)
% 2.07/2.26          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.07/2.26             (k10_relat_1 @ X0 @ (k2_xboole_0 @ (k2_relat_1 @ X0) @ X1))))),
% 2.07/2.26      inference('simplify', [status(thm)], ['10'])).
% 2.07/2.26  thf('12', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf(t1_xboole_1, axiom,
% 2.07/2.26    (![A:$i,B:$i,C:$i]:
% 2.07/2.26     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.07/2.26       ( r1_tarski @ A @ C ) ))).
% 2.07/2.26  thf('13', plain,
% 2.07/2.26      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.07/2.26         (~ (r1_tarski @ X11 @ X12)
% 2.07/2.26          | ~ (r1_tarski @ X12 @ X13)
% 2.07/2.26          | (r1_tarski @ X11 @ X13))),
% 2.07/2.26      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.07/2.26  thf('14', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 2.07/2.26      inference('sup-', [status(thm)], ['12', '13'])).
% 2.07/2.26  thf('15', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ sk_B)
% 2.07/2.26          | (r1_tarski @ sk_A @ 
% 2.07/2.26             (k10_relat_1 @ sk_B @ (k2_xboole_0 @ (k2_relat_1 @ sk_B) @ X0))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['11', '14'])).
% 2.07/2.26  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('17', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         (r1_tarski @ sk_A @ 
% 2.07/2.26          (k10_relat_1 @ sk_B @ (k2_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)))),
% 2.07/2.26      inference('demod', [status(thm)], ['15', '16'])).
% 2.07/2.26  thf(t28_xboole_1, axiom,
% 2.07/2.26    (![A:$i,B:$i]:
% 2.07/2.26     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.07/2.26  thf('18', plain,
% 2.07/2.26      (![X14 : $i, X15 : $i]:
% 2.07/2.26         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 2.07/2.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.07/2.26  thf('19', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         ((k3_xboole_0 @ sk_A @ 
% 2.07/2.26           (k10_relat_1 @ sk_B @ (k2_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)))
% 2.07/2.26           = (sk_A))),
% 2.07/2.26      inference('sup-', [status(thm)], ['17', '18'])).
% 2.07/2.26  thf(t139_funct_1, axiom,
% 2.07/2.26    (![A:$i,B:$i,C:$i]:
% 2.07/2.26     ( ( v1_relat_1 @ C ) =>
% 2.07/2.26       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 2.07/2.26         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.07/2.26  thf('20', plain,
% 2.07/2.26      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.07/2.26         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 2.07/2.26            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 2.07/2.26          | ~ (v1_relat_1 @ X29))),
% 2.07/2.26      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.07/2.26  thf(t167_relat_1, axiom,
% 2.07/2.26    (![A:$i,B:$i]:
% 2.07/2.26     ( ( v1_relat_1 @ B ) =>
% 2.07/2.26       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 2.07/2.26  thf('21', plain,
% 2.07/2.26      (![X22 : $i, X23 : $i]:
% 2.07/2.26         ((r1_tarski @ (k10_relat_1 @ X22 @ X23) @ (k1_relat_1 @ X22))
% 2.07/2.26          | ~ (v1_relat_1 @ X22))),
% 2.07/2.26      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.07/2.26  thf('22', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.07/2.26         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 2.07/2.26           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 2.07/2.26          | ~ (v1_relat_1 @ X1)
% 2.07/2.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 2.07/2.26      inference('sup+', [status(thm)], ['20', '21'])).
% 2.07/2.26  thf('23', plain,
% 2.07/2.26      (![X18 : $i, X19 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 2.07/2.26      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.07/2.26  thf('24', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X1)
% 2.07/2.26          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 2.07/2.26             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 2.07/2.26      inference('clc', [status(thm)], ['22', '23'])).
% 2.07/2.26  thf('25', plain,
% 2.07/2.26      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 2.07/2.26        | ~ (v1_relat_1 @ sk_B))),
% 2.07/2.26      inference('sup+', [status(thm)], ['19', '24'])).
% 2.07/2.26  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('27', plain,
% 2.07/2.26      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.07/2.26      inference('demod', [status(thm)], ['25', '26'])).
% 2.07/2.26  thf('28', plain,
% 2.07/2.26      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.07/2.26         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 2.07/2.26            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 2.07/2.26          | ~ (v1_relat_1 @ X29))),
% 2.07/2.26      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.07/2.26  thf('29', plain,
% 2.07/2.26      (![X24 : $i]:
% 2.07/2.26         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 2.07/2.26          | ~ (v1_relat_1 @ X24))),
% 2.07/2.26      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.07/2.26  thf('30', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         (((k3_xboole_0 @ X0 @ 
% 2.07/2.26            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.07/2.26            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.07/2.26          | ~ (v1_relat_1 @ X1)
% 2.07/2.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.07/2.26      inference('sup+', [status(thm)], ['28', '29'])).
% 2.07/2.26  thf('31', plain,
% 2.07/2.26      (![X18 : $i, X19 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 2.07/2.26      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.07/2.26  thf('32', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X1)
% 2.07/2.26          | ((k3_xboole_0 @ X0 @ 
% 2.07/2.26              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.07/2.26              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.07/2.26      inference('clc', [status(thm)], ['30', '31'])).
% 2.07/2.26  thf(d10_xboole_0, axiom,
% 2.07/2.26    (![A:$i,B:$i]:
% 2.07/2.26     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.07/2.26  thf('33', plain,
% 2.07/2.26      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 2.07/2.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.07/2.26  thf('34', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.07/2.26      inference('simplify', [status(thm)], ['33'])).
% 2.07/2.26  thf(t18_xboole_1, axiom,
% 2.07/2.26    (![A:$i,B:$i,C:$i]:
% 2.07/2.26     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 2.07/2.26  thf('35', plain,
% 2.07/2.26      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.07/2.26         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 2.07/2.26      inference('cnf', [status(esa)], [t18_xboole_1])).
% 2.07/2.26  thf('36', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.07/2.26      inference('sup-', [status(thm)], ['34', '35'])).
% 2.07/2.26  thf('37', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 2.07/2.26          | ~ (v1_relat_1 @ X1))),
% 2.07/2.26      inference('sup+', [status(thm)], ['32', '36'])).
% 2.07/2.26  thf('38', plain,
% 2.07/2.26      (![X2 : $i, X4 : $i]:
% 2.07/2.26         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 2.07/2.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.07/2.26  thf('39', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X1)
% 2.07/2.26          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.07/2.26          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['37', '38'])).
% 2.07/2.26  thf('40', plain,
% 2.07/2.26      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 2.07/2.26        | ~ (v1_relat_1 @ sk_B))),
% 2.07/2.26      inference('sup-', [status(thm)], ['27', '39'])).
% 2.07/2.26  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('42', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.07/2.26      inference('demod', [status(thm)], ['40', '41'])).
% 2.07/2.26  thf('43', plain,
% 2.07/2.26      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.07/2.26         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 2.07/2.26            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 2.07/2.26          | ~ (v1_relat_1 @ X29))),
% 2.07/2.26      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.07/2.26  thf('44', plain,
% 2.07/2.26      (![X22 : $i, X23 : $i]:
% 2.07/2.26         ((r1_tarski @ (k10_relat_1 @ X22 @ X23) @ (k1_relat_1 @ X22))
% 2.07/2.26          | ~ (v1_relat_1 @ X22))),
% 2.07/2.26      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.07/2.26  thf('45', plain,
% 2.07/2.26      (![X14 : $i, X15 : $i]:
% 2.07/2.26         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 2.07/2.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.07/2.26  thf('46', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X0)
% 2.07/2.26          | ((k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 2.07/2.26              = (k10_relat_1 @ X0 @ X1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['44', '45'])).
% 2.07/2.26  thf(commutativity_k3_xboole_0, axiom,
% 2.07/2.26    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.07/2.26  thf('47', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.07/2.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.07/2.26  thf('48', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X0)
% 2.07/2.26          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 2.07/2.26              = (k10_relat_1 @ X0 @ X1)))),
% 2.07/2.26      inference('demod', [status(thm)], ['46', '47'])).
% 2.07/2.26  thf('49', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.07/2.26         (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 2.07/2.26            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 2.07/2.26            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 2.07/2.26          | ~ (v1_relat_1 @ X1)
% 2.07/2.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 2.07/2.26      inference('sup+', [status(thm)], ['43', '48'])).
% 2.07/2.26  thf('50', plain,
% 2.07/2.26      (![X18 : $i, X19 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 2.07/2.26      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.07/2.26  thf('51', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.07/2.26         (~ (v1_relat_1 @ X1)
% 2.07/2.26          | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 2.07/2.26              (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 2.07/2.26              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 2.07/2.26      inference('clc', [status(thm)], ['49', '50'])).
% 2.07/2.26  thf('52', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         (((k3_xboole_0 @ sk_A @ 
% 2.07/2.26            (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 2.07/2.26            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 2.07/2.26          | ~ (v1_relat_1 @ sk_B))),
% 2.07/2.26      inference('sup+', [status(thm)], ['42', '51'])).
% 2.07/2.26  thf('53', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.07/2.26      inference('sup-', [status(thm)], ['34', '35'])).
% 2.07/2.26  thf('54', plain,
% 2.07/2.26      (![X14 : $i, X15 : $i]:
% 2.07/2.26         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 2.07/2.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.07/2.26  thf('55', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 2.07/2.26           = (k3_xboole_0 @ X0 @ X1))),
% 2.07/2.26      inference('sup-', [status(thm)], ['53', '54'])).
% 2.07/2.26  thf('56', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.07/2.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.07/2.26  thf('57', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]:
% 2.07/2.26         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.07/2.26           = (k3_xboole_0 @ X0 @ X1))),
% 2.07/2.26      inference('demod', [status(thm)], ['55', '56'])).
% 2.07/2.26  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('59', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         ((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 2.07/2.26           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))),
% 2.07/2.26      inference('demod', [status(thm)], ['52', '57', '58'])).
% 2.07/2.26  thf('60', plain,
% 2.07/2.26      ((((k3_xboole_0 @ sk_A @ 
% 2.07/2.26          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.07/2.26          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 2.07/2.26        | ~ (v1_relat_1 @ sk_B))),
% 2.07/2.26      inference('sup+', [status(thm)], ['5', '59'])).
% 2.07/2.26  thf('61', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.07/2.26      inference('demod', [status(thm)], ['40', '41'])).
% 2.07/2.26  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('63', plain,
% 2.07/2.26      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.07/2.26         = (sk_A))),
% 2.07/2.26      inference('demod', [status(thm)], ['60', '61', '62'])).
% 2.07/2.26  thf('64', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.07/2.26      inference('simplify', [status(thm)], ['33'])).
% 2.07/2.26  thf('65', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.07/2.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.07/2.26  thf('66', plain,
% 2.07/2.26      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.07/2.26         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 2.07/2.26      inference('cnf', [status(esa)], [t18_xboole_1])).
% 2.07/2.26  thf('67', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.07/2.26         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 2.07/2.26      inference('sup-', [status(thm)], ['65', '66'])).
% 2.07/2.26  thf('68', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.07/2.26      inference('sup-', [status(thm)], ['64', '67'])).
% 2.07/2.26  thf('69', plain,
% 2.07/2.26      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.07/2.26      inference('sup+', [status(thm)], ['63', '68'])).
% 2.07/2.26  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 2.07/2.26  
% 2.07/2.26  % SZS output end Refutation
% 2.07/2.26  
% 2.07/2.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
