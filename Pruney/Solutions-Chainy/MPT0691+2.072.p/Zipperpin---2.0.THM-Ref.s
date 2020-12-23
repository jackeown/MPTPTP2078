%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U0ZiDXnFoY

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:28 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 210 expanded)
%              Number of leaves         :   26 (  71 expanded)
%              Depth                    :   24
%              Number of atoms          :  801 (1808 expanded)
%              Number of equality atoms :   32 (  65 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_relat_1 @ X18 ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_relat_1 @ X18 ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k10_relat_1 @ X21 @ X19 ) @ ( k10_relat_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k3_xboole_0 @ X29 @ ( k10_relat_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X16 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X16 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('44',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X16 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','60'])).

thf('62',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('63',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('66',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X27 @ X28 ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k10_relat_1 @ X23 @ X24 ) @ ( k10_relat_1 @ X22 @ X24 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U0ZiDXnFoY
% 0.13/0.36  % Computer   : n009.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:47:56 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 772 iterations in 0.498s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.93  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.75/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.93  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.75/0.93  thf(t146_funct_1, conjecture,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ B ) =>
% 0.75/0.93       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.75/0.93         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.93    (~( ![A:$i,B:$i]:
% 0.75/0.93        ( ( v1_relat_1 @ B ) =>
% 0.75/0.93          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.75/0.93            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.75/0.93  thf('0', plain,
% 0.75/0.93      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(t148_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ B ) =>
% 0.75/0.93       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.75/0.93  thf('1', plain,
% 0.75/0.93      (![X14 : $i, X15 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.75/0.93          | ~ (v1_relat_1 @ X14))),
% 0.75/0.93      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.75/0.93  thf(t169_relat_1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ A ) =>
% 0.75/0.93       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (![X18 : $i]:
% 0.75/0.93         (((k10_relat_1 @ X18 @ (k2_relat_1 @ X18)) = (k1_relat_1 @ X18))
% 0.75/0.93          | ~ (v1_relat_1 @ X18))),
% 0.75/0.93      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.75/0.93  thf('3', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.75/0.93            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.75/0.93          | ~ (v1_relat_1 @ X1)
% 0.75/0.93          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['1', '2'])).
% 0.75/0.93  thf(dt_k7_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.75/0.93  thf('4', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.75/0.93      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X1)
% 0.75/0.93          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.75/0.93              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.75/0.93      inference('clc', [status(thm)], ['3', '4'])).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.75/0.93      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.75/0.93      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/0.93  thf(d10_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.93  thf('8', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.75/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.93  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.75/0.93      inference('simplify', [status(thm)], ['8'])).
% 0.75/0.93  thf(t12_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.75/0.93  thf('10', plain,
% 0.75/0.93      (![X3 : $i, X4 : $i]:
% 0.75/0.93         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.75/0.93      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.75/0.93  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      (![X18 : $i]:
% 0.75/0.93         (((k10_relat_1 @ X18 @ (k2_relat_1 @ X18)) = (k1_relat_1 @ X18))
% 0.75/0.93          | ~ (v1_relat_1 @ X18))),
% 0.75/0.93      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.75/0.93  thf(t7_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.75/0.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.93  thf(t178_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ C ) =>
% 0.75/0.93       ( ( r1_tarski @ A @ B ) =>
% 0.75/0.93         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.75/0.93  thf('14', plain,
% 0.75/0.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X19 @ X20)
% 0.75/0.93          | ~ (v1_relat_1 @ X21)
% 0.75/0.93          | (r1_tarski @ (k10_relat_1 @ X21 @ X19) @ (k10_relat_1 @ X21 @ X20)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.75/0.93  thf('15', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.75/0.93           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.75/0.93           (k10_relat_1 @ X0 @ (k2_xboole_0 @ (k2_relat_1 @ X0) @ X1)))
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['12', '15'])).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.75/0.93             (k10_relat_1 @ X0 @ (k2_xboole_0 @ (k2_relat_1 @ X0) @ X1))))),
% 0.75/0.93      inference('simplify', [status(thm)], ['16'])).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.75/0.93           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['11', '17'])).
% 0.75/0.93  thf('19', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(t1_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.75/0.93       ( r1_tarski @ A @ C ) ))).
% 0.75/0.93  thf('20', plain,
% 0.75/0.93      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X5 @ X6)
% 0.75/0.93          | ~ (r1_tarski @ X6 @ X7)
% 0.75/0.93          | (r1_tarski @ X5 @ X7))),
% 0.75/0.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.75/0.93  thf('21', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ sk_B)
% 0.75/0.93        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['18', '21'])).
% 0.75/0.93  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('24', plain,
% 0.75/0.93      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.75/0.93      inference('demod', [status(thm)], ['22', '23'])).
% 0.75/0.93  thf(t28_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      (![X8 : $i, X9 : $i]:
% 0.75/0.93         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.75/0.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.93  thf('26', plain,
% 0.75/0.93      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.75/0.93         = (sk_A))),
% 0.75/0.93      inference('sup-', [status(thm)], ['24', '25'])).
% 0.75/0.93  thf(t139_funct_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ C ) =>
% 0.75/0.93       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.75/0.93         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.93         (((k10_relat_1 @ (k7_relat_1 @ X30 @ X29) @ X31)
% 0.75/0.93            = (k3_xboole_0 @ X29 @ (k10_relat_1 @ X30 @ X31)))
% 0.75/0.93          | ~ (v1_relat_1 @ X30))),
% 0.75/0.93      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.75/0.93  thf(t87_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ B ) =>
% 0.75/0.93       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.75/0.93  thf('28', plain,
% 0.75/0.93      (![X25 : $i, X26 : $i]:
% 0.75/0.93         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X25 @ X26)) @ X26)
% 0.75/0.93          | ~ (v1_relat_1 @ X25))),
% 0.75/0.93      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.75/0.93  thf(t167_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ B ) =>
% 0.75/0.93       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.75/0.93  thf('29', plain,
% 0.75/0.93      (![X16 : $i, X17 : $i]:
% 0.75/0.93         ((r1_tarski @ (k10_relat_1 @ X16 @ X17) @ (k1_relat_1 @ X16))
% 0.75/0.93          | ~ (v1_relat_1 @ X16))),
% 0.75/0.93      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.75/0.93  thf('30', plain,
% 0.75/0.93      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X5 @ X6)
% 0.75/0.93          | ~ (r1_tarski @ X6 @ X7)
% 0.75/0.93          | (r1_tarski @ X5 @ X7))),
% 0.75/0.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.75/0.93  thf('31', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.75/0.93          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 0.75/0.93      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.93  thf('32', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X1)
% 0.75/0.93          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['28', '31'])).
% 0.75/0.93  thf('33', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.75/0.93      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/0.93  thf('34', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X1))),
% 0.75/0.93      inference('clc', [status(thm)], ['32', '33'])).
% 0.75/0.93  thf('35', plain,
% 0.75/0.93      (![X0 : $i, X2 : $i]:
% 0.75/0.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.93  thf('36', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X2)
% 0.75/0.93          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 0.75/0.93          | ((X0) = (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['34', '35'])).
% 0.75/0.93  thf('37', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.75/0.93          | ~ (v1_relat_1 @ X1)
% 0.75/0.93          | ((X2) = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 0.75/0.93          | ~ (v1_relat_1 @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['27', '36'])).
% 0.75/0.93  thf('38', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (((X2) = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 0.75/0.93          | ~ (v1_relat_1 @ X1)
% 0.75/0.93          | ~ (r1_tarski @ X2 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))))),
% 0.75/0.93      inference('simplify', [status(thm)], ['37'])).
% 0.75/0.93  thf('39', plain,
% 0.75/0.93      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.75/0.93        | ~ (v1_relat_1 @ sk_B)
% 0.75/0.93        | ((sk_A)
% 0.75/0.93            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['26', '38'])).
% 0.75/0.93  thf('40', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.75/0.93      inference('simplify', [status(thm)], ['8'])).
% 0.75/0.93  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('42', plain,
% 0.75/0.93      (((sk_A)
% 0.75/0.93         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.75/0.93      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.75/0.93  thf('43', plain,
% 0.75/0.93      (![X16 : $i, X17 : $i]:
% 0.75/0.93         ((r1_tarski @ (k10_relat_1 @ X16 @ X17) @ (k1_relat_1 @ X16))
% 0.75/0.93          | ~ (v1_relat_1 @ X16))),
% 0.75/0.93      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.75/0.93  thf('44', plain,
% 0.75/0.93      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.75/0.93        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['42', '43'])).
% 0.75/0.93  thf('45', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ sk_B)
% 0.75/0.93        | (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['7', '44'])).
% 0.75/0.93  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('47', plain,
% 0.75/0.93      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['45', '46'])).
% 0.75/0.93  thf('48', plain,
% 0.75/0.93      (![X25 : $i, X26 : $i]:
% 0.75/0.93         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X25 @ X26)) @ X26)
% 0.75/0.93          | ~ (v1_relat_1 @ X25))),
% 0.75/0.93      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.75/0.93  thf('49', plain,
% 0.75/0.93      (![X0 : $i, X2 : $i]:
% 0.75/0.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.93  thf('50', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X1)
% 0.75/0.93          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.75/0.93          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['48', '49'])).
% 0.75/0.93  thf('51', plain,
% 0.75/0.93      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.75/0.93        | ~ (v1_relat_1 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['47', '50'])).
% 0.75/0.93  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('53', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['51', '52'])).
% 0.75/0.93  thf('54', plain,
% 0.75/0.93      (![X16 : $i, X17 : $i]:
% 0.75/0.93         ((r1_tarski @ (k10_relat_1 @ X16 @ X17) @ (k1_relat_1 @ X16))
% 0.75/0.93          | ~ (v1_relat_1 @ X16))),
% 0.75/0.93      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.75/0.93  thf('55', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 0.75/0.93          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['53', '54'])).
% 0.75/0.93  thf('56', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ sk_B)
% 0.75/0.93          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 0.75/0.93      inference('sup-', [status(thm)], ['6', '55'])).
% 0.75/0.93  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('58', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 0.75/0.93      inference('demod', [status(thm)], ['56', '57'])).
% 0.75/0.93  thf('59', plain,
% 0.75/0.93      (![X0 : $i, X2 : $i]:
% 0.75/0.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.93  thf('60', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 0.75/0.93          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['58', '59'])).
% 0.75/0.93  thf('61', plain,
% 0.75/0.93      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.75/0.93        | ~ (v1_relat_1 @ sk_B)
% 0.75/0.93        | ((sk_A)
% 0.75/0.93            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.75/0.93               (k9_relat_1 @ sk_B @ sk_A))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['5', '60'])).
% 0.75/0.93  thf('62', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['51', '52'])).
% 0.75/0.93  thf('63', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.75/0.93      inference('simplify', [status(thm)], ['8'])).
% 0.75/0.93  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('65', plain,
% 0.75/0.93      (((sk_A)
% 0.75/0.93         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.75/0.93            (k9_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.75/0.93  thf(t88_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.75/0.93  thf('66', plain,
% 0.75/0.93      (![X27 : $i, X28 : $i]:
% 0.75/0.93         ((r1_tarski @ (k7_relat_1 @ X27 @ X28) @ X27) | ~ (v1_relat_1 @ X27))),
% 0.75/0.93      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.75/0.93  thf(t179_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ B ) =>
% 0.75/0.93       ( ![C:$i]:
% 0.75/0.93         ( ( v1_relat_1 @ C ) =>
% 0.75/0.93           ( ( r1_tarski @ B @ C ) =>
% 0.75/0.93             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.75/0.93  thf('67', plain,
% 0.75/0.93      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X22)
% 0.75/0.93          | (r1_tarski @ (k10_relat_1 @ X23 @ X24) @ (k10_relat_1 @ X22 @ X24))
% 0.75/0.93          | ~ (r1_tarski @ X23 @ X22)
% 0.75/0.93          | ~ (v1_relat_1 @ X23))),
% 0.75/0.93      inference('cnf', [status(esa)], [t179_relat_1])).
% 0.75/0.93  thf('68', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.75/0.93          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.75/0.93             (k10_relat_1 @ X0 @ X2))
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['66', '67'])).
% 0.75/0.93  thf('69', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.75/0.93           (k10_relat_1 @ X0 @ X2))
% 0.75/0.93          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['68'])).
% 0.75/0.93  thf('70', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.75/0.93      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/0.93  thf('71', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.75/0.93             (k10_relat_1 @ X0 @ X2)))),
% 0.75/0.93      inference('clc', [status(thm)], ['69', '70'])).
% 0.75/0.93  thf('72', plain,
% 0.75/0.93      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.75/0.93        | ~ (v1_relat_1 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['65', '71'])).
% 0.75/0.93  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('74', plain,
% 0.75/0.93      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['72', '73'])).
% 0.75/0.93  thf('75', plain, ($false), inference('demod', [status(thm)], ['0', '74'])).
% 0.75/0.93  
% 0.75/0.93  % SZS output end Refutation
% 0.75/0.93  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
