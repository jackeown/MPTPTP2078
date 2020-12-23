%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W2JZJQpHJS

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:19 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 177 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   22
%              Number of atoms          :  895 (1479 expanded)
%              Number of equality atoms :   52 (  80 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('6',plain,(
    ! [X22: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X23 @ X24 ) @ ( k10_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','31'])).

thf('33',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('34',plain,(
    ! [X22: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['0','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W2JZJQpHJS
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 1084 iterations in 0.437s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.71/0.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.71/0.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.90  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.71/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.90  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.71/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.71/0.90  thf(t146_funct_1, conjecture,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.71/0.90         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.90    (~( ![A:$i,B:$i]:
% 0.71/0.90        ( ( v1_relat_1 @ B ) =>
% 0.71/0.90          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.71/0.90            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.71/0.90  thf('0', plain,
% 0.71/0.90      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(t139_funct_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ C ) =>
% 0.71/0.90       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.71/0.90         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.71/0.90         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 0.71/0.90            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 0.71/0.90          | ~ (v1_relat_1 @ X26))),
% 0.71/0.90      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.71/0.90  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(t28_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.71/0.90  thf('3', plain,
% 0.71/0.90      (![X10 : $i, X11 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.71/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.71/0.90  thf('4', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.71/0.90  thf(t169_relat_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ A ) =>
% 0.71/0.90       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.71/0.90  thf('5', plain,
% 0.71/0.90      (![X22 : $i]:
% 0.71/0.90         (((k10_relat_1 @ X22 @ (k2_relat_1 @ X22)) = (k1_relat_1 @ X22))
% 0.71/0.90          | ~ (v1_relat_1 @ X22))),
% 0.71/0.90      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.71/0.90  thf('6', plain,
% 0.71/0.90      (![X22 : $i]:
% 0.71/0.90         (((k10_relat_1 @ X22 @ (k2_relat_1 @ X22)) = (k1_relat_1 @ X22))
% 0.71/0.90          | ~ (v1_relat_1 @ X22))),
% 0.71/0.90      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.71/0.90  thf(t170_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( r1_tarski @
% 0.71/0.90         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 0.71/0.90  thf('7', plain,
% 0.71/0.90      (![X23 : $i, X24 : $i]:
% 0.71/0.90         ((r1_tarski @ (k10_relat_1 @ X23 @ X24) @ 
% 0.71/0.90           (k10_relat_1 @ X23 @ (k2_relat_1 @ X23)))
% 0.71/0.90          | ~ (v1_relat_1 @ X23))),
% 0.71/0.90      inference('cnf', [status(esa)], [t170_relat_1])).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.71/0.90           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.71/0.90          | ~ (v1_relat_1 @ X0)
% 0.71/0.90          | ~ (v1_relat_1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['6', '7'])).
% 0.71/0.90  thf('9', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X0)
% 0.71/0.90          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.71/0.90             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.71/0.90      inference('simplify', [status(thm)], ['8'])).
% 0.71/0.90  thf('10', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(t12_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i]:
% 0.71/0.90         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.71/0.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['10', '11'])).
% 0.71/0.90  thf(t11_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.71/0.90  thf('13', plain,
% 0.71/0.90      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.90         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.71/0.90      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.71/0.90  thf('14', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0) | (r1_tarski @ sk_A @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['12', '13'])).
% 0.71/0.90  thf('15', plain,
% 0.71/0.90      ((~ (v1_relat_1 @ sk_B)
% 0.71/0.90        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['9', '14'])).
% 0.71/0.90  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('17', plain,
% 0.71/0.90      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.71/0.90      inference('demod', [status(thm)], ['15', '16'])).
% 0.71/0.90  thf('18', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i]:
% 0.71/0.90         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.71/0.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.71/0.90  thf('19', plain,
% 0.71/0.90      (((k2_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.71/0.90         = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['17', '18'])).
% 0.71/0.90  thf('20', plain,
% 0.71/0.90      ((((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.71/0.90          = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.71/0.90        | ~ (v1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup+', [status(thm)], ['5', '19'])).
% 0.71/0.90  thf('21', plain,
% 0.71/0.90      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['10', '11'])).
% 0.71/0.90  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('23', plain,
% 0.71/0.90      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.71/0.90      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.71/0.90  thf('24', plain,
% 0.71/0.90      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.71/0.90         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 0.71/0.90            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 0.71/0.90          | ~ (v1_relat_1 @ X26))),
% 0.71/0.90      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.71/0.90  thf(t167_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.71/0.90  thf('25', plain,
% 0.71/0.90      (![X20 : $i, X21 : $i]:
% 0.71/0.90         ((r1_tarski @ (k10_relat_1 @ X20 @ X21) @ (k1_relat_1 @ X20))
% 0.71/0.90          | ~ (v1_relat_1 @ X20))),
% 0.71/0.90      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.71/0.90  thf('26', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.71/0.90           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 0.71/0.90          | ~ (v1_relat_1 @ X1)
% 0.71/0.90          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['24', '25'])).
% 0.71/0.90  thf(dt_k7_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.71/0.90  thf('27', plain,
% 0.71/0.90      (![X16 : $i, X17 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.71/0.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.71/0.90  thf('28', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X1)
% 0.71/0.90          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.71/0.90             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 0.71/0.90      inference('clc', [status(thm)], ['26', '27'])).
% 0.71/0.90  thf('29', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 0.71/0.90           (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 0.71/0.90          | ~ (v1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup+', [status(thm)], ['23', '28'])).
% 0.71/0.90  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('31', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 0.71/0.90          (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['29', '30'])).
% 0.71/0.90  thf('32', plain,
% 0.71/0.90      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['4', '31'])).
% 0.71/0.90  thf('33', plain,
% 0.71/0.90      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.71/0.90         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 0.71/0.90            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 0.71/0.90          | ~ (v1_relat_1 @ X26))),
% 0.71/0.90      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.71/0.90  thf('34', plain,
% 0.71/0.90      (![X22 : $i]:
% 0.71/0.90         (((k10_relat_1 @ X22 @ (k2_relat_1 @ X22)) = (k1_relat_1 @ X22))
% 0.71/0.90          | ~ (v1_relat_1 @ X22))),
% 0.71/0.90      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.71/0.90  thf('35', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X0 @ 
% 0.71/0.90            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.71/0.90            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.71/0.90          | ~ (v1_relat_1 @ X1)
% 0.71/0.90          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['33', '34'])).
% 0.71/0.90  thf('36', plain,
% 0.71/0.90      (![X16 : $i, X17 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.71/0.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.71/0.90  thf('37', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X1)
% 0.71/0.90          | ((k3_xboole_0 @ X0 @ 
% 0.71/0.90              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.71/0.90              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.71/0.90      inference('clc', [status(thm)], ['35', '36'])).
% 0.71/0.90  thf(t17_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.71/0.90  thf('38', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.71/0.90      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.71/0.90  thf('39', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.71/0.90          | ~ (v1_relat_1 @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['37', '38'])).
% 0.71/0.90  thf(d10_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.71/0.90  thf('40', plain,
% 0.71/0.90      (![X0 : $i, X2 : $i]:
% 0.71/0.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.71/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.71/0.90  thf('41', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X1)
% 0.71/0.90          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.71/0.90          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['39', '40'])).
% 0.71/0.90  thf('42', plain,
% 0.71/0.90      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.71/0.90        | ~ (v1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['32', '41'])).
% 0.71/0.90  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('44', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['42', '43'])).
% 0.71/0.90  thf(t148_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.71/0.90  thf('45', plain,
% 0.71/0.90      (![X18 : $i, X19 : $i]:
% 0.71/0.90         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 0.71/0.90          | ~ (v1_relat_1 @ X18))),
% 0.71/0.90      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.71/0.90  thf('46', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X0)
% 0.71/0.90          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.71/0.90             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.71/0.90      inference('simplify', [status(thm)], ['8'])).
% 0.71/0.90  thf('47', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.71/0.90           (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 0.71/0.90          | ~ (v1_relat_1 @ X1)
% 0.71/0.90          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['45', '46'])).
% 0.71/0.90  thf('48', plain,
% 0.71/0.90      (![X16 : $i, X17 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.71/0.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.71/0.90  thf('49', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X1)
% 0.71/0.90          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.71/0.90             (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))))),
% 0.71/0.90      inference('clc', [status(thm)], ['47', '48'])).
% 0.71/0.90  thf('50', plain,
% 0.71/0.90      (((r1_tarski @ sk_A @ 
% 0.71/0.90         (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.71/0.90        | ~ (v1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup+', [status(thm)], ['44', '49'])).
% 0.71/0.90  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('52', plain,
% 0.71/0.90      ((r1_tarski @ sk_A @ 
% 0.71/0.90        (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['50', '51'])).
% 0.71/0.90  thf('53', plain,
% 0.71/0.90      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.71/0.90         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 0.71/0.90            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 0.71/0.90          | ~ (v1_relat_1 @ X26))),
% 0.71/0.90      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.71/0.90  thf('54', plain,
% 0.71/0.90      (![X20 : $i, X21 : $i]:
% 0.71/0.90         ((r1_tarski @ (k10_relat_1 @ X20 @ X21) @ (k1_relat_1 @ X20))
% 0.71/0.90          | ~ (v1_relat_1 @ X20))),
% 0.71/0.90      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.71/0.90  thf('55', plain,
% 0.71/0.90      (![X10 : $i, X11 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.71/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.71/0.90  thf('56', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X0)
% 0.71/0.90          | ((k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.71/0.90              = (k10_relat_1 @ X0 @ X1)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['54', '55'])).
% 0.71/0.90  thf(commutativity_k2_tarski, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.71/0.90  thf('57', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.71/0.90  thf(t12_setfam_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.71/0.90  thf('58', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.71/0.90      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.71/0.90  thf('59', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['57', '58'])).
% 0.71/0.90  thf('60', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.71/0.90      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.71/0.90  thf('61', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['59', '60'])).
% 0.71/0.90  thf('62', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X0)
% 0.71/0.90          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.71/0.90              = (k10_relat_1 @ X0 @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['56', '61'])).
% 0.71/0.90  thf('63', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 0.71/0.90            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.71/0.90            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ X1)
% 0.71/0.90          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['53', '62'])).
% 0.71/0.90  thf('64', plain,
% 0.71/0.90      (![X16 : $i, X17 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.71/0.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.71/0.90  thf('65', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X1)
% 0.71/0.90          | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 0.71/0.90              (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.71/0.90              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 0.71/0.90      inference('clc', [status(thm)], ['63', '64'])).
% 0.71/0.90  thf('66', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.71/0.90      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.71/0.90  thf('67', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['59', '60'])).
% 0.71/0.90  thf('68', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.71/0.90      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.71/0.90  thf('69', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i]:
% 0.71/0.90         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.71/0.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.71/0.90  thf('70', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['68', '69'])).
% 0.71/0.90  thf('71', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['67', '70'])).
% 0.71/0.90  thf('72', plain,
% 0.71/0.90      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.90         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.71/0.90      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.71/0.90  thf('73', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['71', '72'])).
% 0.71/0.90  thf('74', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0)),
% 0.71/0.90      inference('sup-', [status(thm)], ['66', '73'])).
% 0.71/0.90  thf('75', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X1)
% 0.71/0.90          | ~ (v1_relat_1 @ X2))),
% 0.71/0.90      inference('sup+', [status(thm)], ['65', '74'])).
% 0.71/0.90  thf('76', plain,
% 0.71/0.90      (![X0 : $i, X2 : $i]:
% 0.71/0.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.71/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.71/0.90  thf('77', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X2)
% 0.71/0.90          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 0.71/0.90          | ((X0) = (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['75', '76'])).
% 0.71/0.90  thf('78', plain,
% 0.71/0.90      ((((sk_A)
% 0.71/0.90          = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.71/0.90             (k9_relat_1 @ sk_B @ sk_A)))
% 0.71/0.90        | ~ (v1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['52', '77'])).
% 0.71/0.90  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('80', plain,
% 0.71/0.90      (((sk_A)
% 0.71/0.90         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.71/0.90            (k9_relat_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['78', '79'])).
% 0.71/0.90  thf('81', plain,
% 0.71/0.90      ((((sk_A)
% 0.71/0.90          = (k3_xboole_0 @ sk_A @ 
% 0.71/0.90             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.71/0.90        | ~ (v1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup+', [status(thm)], ['1', '80'])).
% 0.71/0.90  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('83', plain,
% 0.71/0.90      (((sk_A)
% 0.71/0.90         = (k3_xboole_0 @ sk_A @ 
% 0.71/0.90            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.71/0.90      inference('demod', [status(thm)], ['81', '82'])).
% 0.71/0.90  thf('84', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['59', '60'])).
% 0.71/0.90  thf('85', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.71/0.90      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.71/0.90  thf('86', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.71/0.90      inference('sup+', [status(thm)], ['84', '85'])).
% 0.71/0.90  thf('87', plain,
% 0.71/0.90      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['83', '86'])).
% 0.71/0.90  thf('88', plain, ($false), inference('demod', [status(thm)], ['0', '87'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
