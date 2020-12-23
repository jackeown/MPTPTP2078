%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zOwQlzjYpd

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:23 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 266 expanded)
%              Number of leaves         :   23 (  97 expanded)
%              Depth                    :   24
%              Number of atoms          :  907 (2238 expanded)
%              Number of equality atoms :   74 ( 185 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) @ X20 )
        = ( k3_xboole_0 @ X18 @ ( k10_relat_1 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( ( k7_relat_1 @ X16 @ X17 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('11',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X7: $i] :
      ( ( ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) @ X8 )
        = ( k9_relat_1 @ X10 @ X8 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X11: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_relat_1 @ X11 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('34',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('37',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('39',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('41',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( ( k7_relat_1 @ X16 @ X17 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('55',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['35','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('64',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('70',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('72',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('74',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('75',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('76',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['61','62','63','76','77'])).

thf('79',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','78'])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['2','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('87',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['0','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zOwQlzjYpd
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:33:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 202 iterations in 0.122s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.58  thf(t146_funct_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.58         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i]:
% 0.38/0.58        ( ( v1_relat_1 @ B ) =>
% 0.38/0.58          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.58            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t139_funct_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ C ) =>
% 0.38/0.58       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.38/0.58         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.58         (((k10_relat_1 @ (k7_relat_1 @ X19 @ X18) @ X20)
% 0.38/0.58            = (k3_xboole_0 @ X18 @ (k10_relat_1 @ X19 @ X20)))
% 0.38/0.58          | ~ (v1_relat_1 @ X19))),
% 0.38/0.58      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.38/0.58  thf(dt_k7_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.38/0.58  thf('3', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t71_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.58       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.58  thf('4', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf(t97_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.38/0.58         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.38/0.58          | ((k7_relat_1 @ X16 @ X17) = (X16))
% 0.38/0.58          | ~ (v1_relat_1 @ X16))),
% 0.38/0.58      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ X1)
% 0.38/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.58          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.58  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.38/0.58  thf('7', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ X1)
% 0.38/0.58          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.38/0.58         = (k6_relat_1 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['3', '8'])).
% 0.38/0.58  thf(t90_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.38/0.58         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.38/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      ((((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.38/0.58          = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ 
% 0.38/0.58             (k1_relat_1 @ sk_B)))
% 0.38/0.58        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('12', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf('13', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf('14', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.58  thf('15', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.38/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.38/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.38/0.58  thf(t146_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X7 : $i]:
% 0.38/0.58         (((k9_relat_1 @ X7 @ (k1_relat_1 @ X7)) = (k2_relat_1 @ X7))
% 0.38/0.58          | ~ (v1_relat_1 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.38/0.58            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.58            = (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.38/0.58          | ~ (v1_relat_1 @ X1)
% 0.38/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X1)
% 0.38/0.58          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.38/0.58              (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.58              = (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.38/0.58      inference('clc', [status(thm)], ['19', '20'])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf(t17_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.38/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.38/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.58  thf(t162_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ![B:$i,C:$i]:
% 0.38/0.58         ( ( r1_tarski @ B @ C ) =>
% 0.38/0.58           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.38/0.58             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X8 @ X9)
% 0.38/0.58          | ((k9_relat_1 @ (k7_relat_1 @ X10 @ X9) @ X8)
% 0.38/0.58              = (k9_relat_1 @ X10 @ X8))
% 0.38/0.58          | ~ (v1_relat_1 @ X10))),
% 0.38/0.58      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X2)
% 0.38/0.58          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.58              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.38/0.58            = (k9_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.38/0.58          | ~ (v1_relat_1 @ X1)
% 0.38/0.58          | ~ (v1_relat_1 @ X1))),
% 0.38/0.58      inference('sup+', [status(thm)], ['21', '26'])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X1)
% 0.38/0.58          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.38/0.58              = (k9_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 0.38/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.38/0.58            = (k9_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['16', '28'])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k9_relat_1 @ sk_B @ sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.58      inference('sup+', [status(thm)], ['15', '29'])).
% 0.38/0.58  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k9_relat_1 @ sk_B @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.58  thf(t169_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X11 : $i]:
% 0.38/0.58         (((k10_relat_1 @ X11 @ (k2_relat_1 @ X11)) = (k1_relat_1 @ X11))
% 0.38/0.58          | ~ (v1_relat_1 @ X11))),
% 0.38/0.58      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.38/0.58          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.38/0.58        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['32', '33'])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.38/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.38/0.58  thf('37', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.38/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.58  thf('39', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.38/0.58      inference('sup+', [status(thm)], ['37', '38'])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.38/0.58  thf('41', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.38/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.38/0.58          | ((k7_relat_1 @ X16 @ X17) = (X16))
% 0.38/0.58          | ~ (v1_relat_1 @ X16))),
% 0.38/0.58      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2)
% 0.38/0.58          | ~ (v1_relat_1 @ X1)
% 0.38/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.38/0.58          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.38/0.58              = (k7_relat_1 @ X1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 0.38/0.58          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2)
% 0.38/0.58              = (k7_relat_1 @ X0 @ X1))
% 0.38/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['42', '45'])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r1_tarski @ sk_A @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ sk_B)
% 0.38/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.38/0.58          | ((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)
% 0.38/0.58              = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['41', '46'])).
% 0.38/0.58  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r1_tarski @ sk_A @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.38/0.58          | ((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)
% 0.38/0.58              = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ sk_B)
% 0.38/0.58          | ((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)
% 0.38/0.58              = (k7_relat_1 @ sk_B @ sk_A))
% 0.38/0.58          | ~ (r1_tarski @ sk_A @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['40', '49'])).
% 0.38/0.58  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)
% 0.38/0.58            = (k7_relat_1 @ sk_B @ sk_A))
% 0.38/0.58          | ~ (r1_tarski @ sk_A @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['50', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.58         = (k7_relat_1 @ sk_B @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['39', '52'])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.38/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.38/0.58          = (k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['53', '54'])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.38/0.58          = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.38/0.58        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['55', '56'])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.58        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.38/0.58            = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['36', '57'])).
% 0.38/0.58  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.38/0.58         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.38/0.58  thf('61', plain,
% 0.38/0.58      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.38/0.58          = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.58      inference('sup+', [status(thm)], ['35', '60'])).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('63', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.38/0.58  thf('64', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.38/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.58  thf('66', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ X1)
% 0.38/0.58          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 0.38/0.58           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.38/0.58  thf('68', plain,
% 0.38/0.58      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_A)
% 0.38/0.58         = (k6_relat_1 @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['64', '67'])).
% 0.38/0.58  thf('69', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.38/0.58  thf('70', plain,
% 0.38/0.58      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_A) = (k6_relat_1 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['68', '69'])).
% 0.38/0.58  thf('71', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.38/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.38/0.58  thf('72', plain,
% 0.38/0.58      ((((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.38/0.58          = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['70', '71'])).
% 0.38/0.58  thf('73', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf('74', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf('75', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.58  thf('76', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.38/0.58  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('78', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['61', '62', '63', '76', '77'])).
% 0.38/0.58  thf('79', plain,
% 0.38/0.58      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.38/0.58          = (sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['34', '78'])).
% 0.38/0.58  thf('80', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.58        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.38/0.58            (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['2', '79'])).
% 0.38/0.58  thf('81', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('82', plain,
% 0.38/0.58      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.38/0.58         = (sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['80', '81'])).
% 0.38/0.58  thf('83', plain,
% 0.38/0.58      ((((k3_xboole_0 @ sk_A @ 
% 0.38/0.58          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.58      inference('sup+', [status(thm)], ['1', '82'])).
% 0.38/0.58  thf('84', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('85', plain,
% 0.38/0.58      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.38/0.58         = (sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['83', '84'])).
% 0.38/0.58  thf('86', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.38/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.58  thf('87', plain,
% 0.38/0.58      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['85', '86'])).
% 0.38/0.58  thf('88', plain, ($false), inference('demod', [status(thm)], ['0', '87'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
