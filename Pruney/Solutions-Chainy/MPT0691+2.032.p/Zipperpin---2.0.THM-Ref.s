%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yVy8RyU09b

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:22 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 213 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :   22
%              Number of atoms          :  771 (1807 expanded)
%              Number of equality atoms :   51 (  96 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k9_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X29: $i] :
      ( ( ( k10_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X29: $i] :
      ( ( ( k10_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( r1_tarski @ ( k2_xboole_0 @ X17 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('21',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X39 ) @ X40 )
      | ( ( k7_relat_1 @ X39 @ X40 )
        = X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('26',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k3_xboole_0 @ X41 @ ( k10_relat_1 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ X0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ X0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','29'])).

thf('31',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k3_xboole_0 @ X41 @ ( k10_relat_1 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X27 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','43'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('45',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) ) @ X36 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('46',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k3_xboole_0 @ X41 @ ( k10_relat_1 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('52',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X27 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['50','59'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['60','65','66'])).

thf('68',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','67'])).

thf('69',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('73',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yVy8RyU09b
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:25:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.09/1.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.09/1.26  % Solved by: fo/fo7.sh
% 1.09/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.09/1.26  % done 1931 iterations in 0.802s
% 1.09/1.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.09/1.26  % SZS output start Refutation
% 1.09/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.09/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.09/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.09/1.26  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.09/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.09/1.26  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.09/1.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.09/1.26  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.09/1.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.09/1.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.09/1.26  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.09/1.26  thf(t146_funct_1, conjecture,
% 1.09/1.26    (![A:$i,B:$i]:
% 1.09/1.26     ( ( v1_relat_1 @ B ) =>
% 1.09/1.26       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.09/1.26         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.09/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.09/1.26    (~( ![A:$i,B:$i]:
% 1.09/1.26        ( ( v1_relat_1 @ B ) =>
% 1.09/1.26          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.09/1.26            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.09/1.26    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.09/1.26  thf('0', plain,
% 1.09/1.26      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf(t148_relat_1, axiom,
% 1.09/1.26    (![A:$i,B:$i]:
% 1.09/1.26     ( ( v1_relat_1 @ B ) =>
% 1.09/1.26       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.09/1.26  thf('1', plain,
% 1.09/1.26      (![X22 : $i, X23 : $i]:
% 1.09/1.26         (((k2_relat_1 @ (k7_relat_1 @ X22 @ X23)) = (k9_relat_1 @ X22 @ X23))
% 1.09/1.26          | ~ (v1_relat_1 @ X22))),
% 1.09/1.26      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.09/1.26  thf(t169_relat_1, axiom,
% 1.09/1.26    (![A:$i]:
% 1.09/1.26     ( ( v1_relat_1 @ A ) =>
% 1.09/1.26       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.09/1.26  thf('2', plain,
% 1.09/1.26      (![X29 : $i]:
% 1.09/1.26         (((k10_relat_1 @ X29 @ (k2_relat_1 @ X29)) = (k1_relat_1 @ X29))
% 1.09/1.26          | ~ (v1_relat_1 @ X29))),
% 1.09/1.26      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.09/1.26  thf('3', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]:
% 1.09/1.26         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.09/1.26            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.09/1.26          | ~ (v1_relat_1 @ X1)
% 1.09/1.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.09/1.26      inference('sup+', [status(thm)], ['1', '2'])).
% 1.09/1.26  thf(dt_k7_relat_1, axiom,
% 1.09/1.26    (![A:$i,B:$i]:
% 1.09/1.26     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.09/1.26  thf('4', plain,
% 1.09/1.26      (![X20 : $i, X21 : $i]:
% 1.09/1.26         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 1.09/1.26      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.09/1.26  thf('5', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]:
% 1.09/1.26         (~ (v1_relat_1 @ X1)
% 1.09/1.26          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.09/1.26              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.09/1.26      inference('clc', [status(thm)], ['3', '4'])).
% 1.09/1.26  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf(t28_xboole_1, axiom,
% 1.09/1.26    (![A:$i,B:$i]:
% 1.09/1.26     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.09/1.26  thf('7', plain,
% 1.09/1.26      (![X13 : $i, X14 : $i]:
% 1.09/1.26         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.09/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.09/1.26  thf('8', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 1.09/1.26      inference('sup-', [status(thm)], ['6', '7'])).
% 1.09/1.26  thf('9', plain,
% 1.09/1.26      (![X29 : $i]:
% 1.09/1.26         (((k10_relat_1 @ X29 @ (k2_relat_1 @ X29)) = (k1_relat_1 @ X29))
% 1.09/1.26          | ~ (v1_relat_1 @ X29))),
% 1.09/1.26      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.09/1.26  thf('10', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf(d10_xboole_0, axiom,
% 1.09/1.26    (![A:$i,B:$i]:
% 1.09/1.26     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.09/1.26  thf('11', plain,
% 1.09/1.26      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.09/1.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.09/1.26  thf('12', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.09/1.26      inference('simplify', [status(thm)], ['11'])).
% 1.09/1.26  thf(t8_xboole_1, axiom,
% 1.09/1.26    (![A:$i,B:$i,C:$i]:
% 1.09/1.26     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.09/1.26       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.09/1.26  thf('13', plain,
% 1.09/1.26      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.09/1.26         (~ (r1_tarski @ X17 @ X18)
% 1.09/1.26          | ~ (r1_tarski @ X19 @ X18)
% 1.09/1.26          | (r1_tarski @ (k2_xboole_0 @ X17 @ X19) @ X18))),
% 1.09/1.26      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.09/1.26  thf('14', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]:
% 1.09/1.26         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 1.09/1.26      inference('sup-', [status(thm)], ['12', '13'])).
% 1.09/1.26  thf('15', plain,
% 1.09/1.26      ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 1.09/1.26        (k1_relat_1 @ sk_B))),
% 1.09/1.26      inference('sup-', [status(thm)], ['10', '14'])).
% 1.09/1.26  thf(t7_xboole_1, axiom,
% 1.09/1.26    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.09/1.26  thf('16', plain,
% 1.09/1.26      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 1.09/1.26      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.09/1.26  thf('17', plain,
% 1.09/1.26      (![X2 : $i, X4 : $i]:
% 1.09/1.26         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.09/1.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.09/1.26  thf('18', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]:
% 1.09/1.26         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.09/1.26          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.09/1.26      inference('sup-', [status(thm)], ['16', '17'])).
% 1.09/1.26  thf('19', plain,
% 1.09/1.26      (((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.09/1.26      inference('sup-', [status(thm)], ['15', '18'])).
% 1.09/1.26  thf('20', plain,
% 1.09/1.26      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 1.09/1.26      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.09/1.26  thf(t97_relat_1, axiom,
% 1.09/1.26    (![A:$i,B:$i]:
% 1.09/1.26     ( ( v1_relat_1 @ B ) =>
% 1.09/1.26       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.09/1.26         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.09/1.26  thf('21', plain,
% 1.09/1.26      (![X39 : $i, X40 : $i]:
% 1.09/1.26         (~ (r1_tarski @ (k1_relat_1 @ X39) @ X40)
% 1.09/1.26          | ((k7_relat_1 @ X39 @ X40) = (X39))
% 1.09/1.26          | ~ (v1_relat_1 @ X39))),
% 1.09/1.26      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.09/1.26  thf('22', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]:
% 1.09/1.26         (~ (v1_relat_1 @ X1)
% 1.09/1.26          | ((k7_relat_1 @ X1 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0)) = (X1)))),
% 1.09/1.26      inference('sup-', [status(thm)], ['20', '21'])).
% 1.09/1.26  thf('23', plain,
% 1.09/1.26      ((((k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (sk_B))
% 1.09/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.09/1.26      inference('sup+', [status(thm)], ['19', '22'])).
% 1.09/1.26  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('25', plain, (((k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (sk_B))),
% 1.09/1.26      inference('demod', [status(thm)], ['23', '24'])).
% 1.09/1.26  thf(t139_funct_1, axiom,
% 1.09/1.26    (![A:$i,B:$i,C:$i]:
% 1.09/1.26     ( ( v1_relat_1 @ C ) =>
% 1.09/1.26       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.09/1.26         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.09/1.26  thf('26', plain,
% 1.09/1.26      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.09/1.26         (((k10_relat_1 @ (k7_relat_1 @ X42 @ X41) @ X43)
% 1.09/1.26            = (k3_xboole_0 @ X41 @ (k10_relat_1 @ X42 @ X43)))
% 1.09/1.26          | ~ (v1_relat_1 @ X42))),
% 1.09/1.26      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.09/1.26  thf('27', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         (((k10_relat_1 @ sk_B @ X0)
% 1.09/1.26            = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0)))
% 1.09/1.26          | ~ (v1_relat_1 @ sk_B))),
% 1.09/1.26      inference('sup+', [status(thm)], ['25', '26'])).
% 1.09/1.26  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('29', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         ((k10_relat_1 @ sk_B @ X0)
% 1.09/1.26           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0)))),
% 1.09/1.26      inference('demod', [status(thm)], ['27', '28'])).
% 1.09/1.26  thf('30', plain,
% 1.09/1.26      ((((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))
% 1.09/1.26          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))
% 1.09/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.09/1.26      inference('sup+', [status(thm)], ['9', '29'])).
% 1.09/1.26  thf('31', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.09/1.26      inference('simplify', [status(thm)], ['11'])).
% 1.09/1.26  thf('32', plain,
% 1.09/1.26      (![X13 : $i, X14 : $i]:
% 1.09/1.26         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.09/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.09/1.26  thf('33', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.09/1.26      inference('sup-', [status(thm)], ['31', '32'])).
% 1.09/1.26  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('35', plain,
% 1.09/1.26      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 1.09/1.26      inference('demod', [status(thm)], ['30', '33', '34'])).
% 1.09/1.26  thf('36', plain,
% 1.09/1.26      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.09/1.26         (((k10_relat_1 @ (k7_relat_1 @ X42 @ X41) @ X43)
% 1.09/1.26            = (k3_xboole_0 @ X41 @ (k10_relat_1 @ X42 @ X43)))
% 1.09/1.26          | ~ (v1_relat_1 @ X42))),
% 1.09/1.26      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.09/1.26  thf(t167_relat_1, axiom,
% 1.09/1.26    (![A:$i,B:$i]:
% 1.09/1.26     ( ( v1_relat_1 @ B ) =>
% 1.09/1.26       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.09/1.26  thf('37', plain,
% 1.09/1.26      (![X27 : $i, X28 : $i]:
% 1.09/1.26         ((r1_tarski @ (k10_relat_1 @ X27 @ X28) @ (k1_relat_1 @ X27))
% 1.09/1.26          | ~ (v1_relat_1 @ X27))),
% 1.09/1.26      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.09/1.26  thf('38', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.26         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.09/1.26           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 1.09/1.26          | ~ (v1_relat_1 @ X1)
% 1.09/1.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 1.09/1.26      inference('sup+', [status(thm)], ['36', '37'])).
% 1.09/1.26  thf('39', plain,
% 1.09/1.26      (![X20 : $i, X21 : $i]:
% 1.09/1.26         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 1.09/1.26      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.09/1.26  thf('40', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.26         (~ (v1_relat_1 @ X1)
% 1.09/1.26          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.09/1.26             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 1.09/1.26      inference('clc', [status(thm)], ['38', '39'])).
% 1.09/1.26  thf('41', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.09/1.26           (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 1.09/1.26          | ~ (v1_relat_1 @ sk_B))),
% 1.09/1.26      inference('sup+', [status(thm)], ['35', '40'])).
% 1.09/1.26  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('43', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.09/1.26          (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 1.09/1.26      inference('demod', [status(thm)], ['41', '42'])).
% 1.09/1.26  thf('44', plain,
% 1.09/1.26      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.09/1.26      inference('sup+', [status(thm)], ['8', '43'])).
% 1.09/1.26  thf(t87_relat_1, axiom,
% 1.09/1.26    (![A:$i,B:$i]:
% 1.09/1.26     ( ( v1_relat_1 @ B ) =>
% 1.09/1.26       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.09/1.26  thf('45', plain,
% 1.09/1.26      (![X35 : $i, X36 : $i]:
% 1.09/1.26         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X35 @ X36)) @ X36)
% 1.09/1.26          | ~ (v1_relat_1 @ X35))),
% 1.09/1.26      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.09/1.26  thf('46', plain,
% 1.09/1.26      (![X2 : $i, X4 : $i]:
% 1.09/1.26         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.09/1.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.09/1.26  thf('47', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]:
% 1.09/1.26         (~ (v1_relat_1 @ X1)
% 1.09/1.26          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.09/1.26          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.09/1.26      inference('sup-', [status(thm)], ['45', '46'])).
% 1.09/1.26  thf('48', plain,
% 1.09/1.26      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.09/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.09/1.26      inference('sup-', [status(thm)], ['44', '47'])).
% 1.09/1.26  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('50', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.09/1.26      inference('demod', [status(thm)], ['48', '49'])).
% 1.09/1.26  thf('51', plain,
% 1.09/1.26      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.09/1.26         (((k10_relat_1 @ (k7_relat_1 @ X42 @ X41) @ X43)
% 1.09/1.26            = (k3_xboole_0 @ X41 @ (k10_relat_1 @ X42 @ X43)))
% 1.09/1.26          | ~ (v1_relat_1 @ X42))),
% 1.09/1.26      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.09/1.26  thf('52', plain,
% 1.09/1.26      (![X27 : $i, X28 : $i]:
% 1.09/1.26         ((r1_tarski @ (k10_relat_1 @ X27 @ X28) @ (k1_relat_1 @ X27))
% 1.09/1.26          | ~ (v1_relat_1 @ X27))),
% 1.09/1.26      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.09/1.26  thf('53', plain,
% 1.09/1.26      (![X13 : $i, X14 : $i]:
% 1.09/1.26         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.09/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.09/1.26  thf('54', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]:
% 1.09/1.26         (~ (v1_relat_1 @ X0)
% 1.09/1.26          | ((k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.09/1.26              = (k10_relat_1 @ X0 @ X1)))),
% 1.09/1.26      inference('sup-', [status(thm)], ['52', '53'])).
% 1.09/1.26  thf(commutativity_k3_xboole_0, axiom,
% 1.09/1.26    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.09/1.26  thf('55', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.09/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.09/1.26  thf('56', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]:
% 1.09/1.26         (~ (v1_relat_1 @ X0)
% 1.09/1.26          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 1.09/1.26              = (k10_relat_1 @ X0 @ X1)))),
% 1.09/1.26      inference('demod', [status(thm)], ['54', '55'])).
% 1.09/1.26  thf('57', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.26         (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 1.09/1.26            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 1.09/1.26            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 1.09/1.26          | ~ (v1_relat_1 @ X1)
% 1.09/1.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 1.09/1.26      inference('sup+', [status(thm)], ['51', '56'])).
% 1.09/1.26  thf('58', plain,
% 1.09/1.26      (![X20 : $i, X21 : $i]:
% 1.09/1.26         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 1.09/1.26      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.09/1.26  thf('59', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.26         (~ (v1_relat_1 @ X1)
% 1.09/1.26          | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 1.09/1.26              (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 1.09/1.26              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 1.09/1.26      inference('clc', [status(thm)], ['57', '58'])).
% 1.09/1.26  thf('60', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         (((k3_xboole_0 @ sk_A @ 
% 1.09/1.26            (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 1.09/1.26            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 1.09/1.26          | ~ (v1_relat_1 @ sk_B))),
% 1.09/1.26      inference('sup+', [status(thm)], ['50', '59'])).
% 1.09/1.26  thf(t17_xboole_1, axiom,
% 1.09/1.26    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.09/1.26  thf('61', plain,
% 1.09/1.26      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 1.09/1.26      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.09/1.26  thf('62', plain,
% 1.09/1.26      (![X13 : $i, X14 : $i]:
% 1.09/1.26         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.09/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.09/1.26  thf('63', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]:
% 1.09/1.26         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.09/1.26           = (k3_xboole_0 @ X0 @ X1))),
% 1.09/1.26      inference('sup-', [status(thm)], ['61', '62'])).
% 1.09/1.26  thf('64', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.09/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.09/1.26  thf('65', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]:
% 1.09/1.26         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.09/1.26           = (k3_xboole_0 @ X0 @ X1))),
% 1.09/1.26      inference('demod', [status(thm)], ['63', '64'])).
% 1.09/1.26  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('67', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         ((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 1.09/1.26           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))),
% 1.09/1.26      inference('demod', [status(thm)], ['60', '65', '66'])).
% 1.09/1.26  thf('68', plain,
% 1.09/1.26      ((((k3_xboole_0 @ sk_A @ 
% 1.09/1.26          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.09/1.26          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.09/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.09/1.26      inference('sup+', [status(thm)], ['5', '67'])).
% 1.09/1.26  thf('69', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.09/1.26      inference('demod', [status(thm)], ['48', '49'])).
% 1.09/1.26  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('71', plain,
% 1.09/1.26      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.09/1.26         = (sk_A))),
% 1.09/1.26      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.09/1.26  thf('72', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.09/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.09/1.26  thf('73', plain,
% 1.09/1.26      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 1.09/1.26      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.09/1.26  thf('74', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.09/1.26      inference('sup+', [status(thm)], ['72', '73'])).
% 1.09/1.26  thf('75', plain,
% 1.09/1.26      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.09/1.26      inference('sup+', [status(thm)], ['71', '74'])).
% 1.09/1.26  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 1.09/1.26  
% 1.09/1.26  % SZS output end Refutation
% 1.09/1.26  
% 1.09/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
