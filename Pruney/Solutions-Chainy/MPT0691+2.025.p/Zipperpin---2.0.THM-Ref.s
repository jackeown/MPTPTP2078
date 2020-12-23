%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4E1NZSejuH

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 337 expanded)
%              Number of leaves         :   25 ( 122 expanded)
%              Depth                    :   24
%              Number of atoms          :  806 (3016 expanded)
%              Number of equality atoms :   66 ( 241 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X12 @ X11 ) @ X10 )
        = ( k9_relat_1 @ X12 @ X10 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( ( k7_relat_1 @ X18 @ X19 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','26'])).

thf('28',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('30',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('38',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','35','36','37','38'])).

thf('40',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('44',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('54',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('58',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('63',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('65',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('66',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('67',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','67','68','69'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['50','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4E1NZSejuH
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 164 iterations in 0.100s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.55  thf(t146_funct_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.55         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( v1_relat_1 @ B ) =>
% 0.21/0.55          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.55            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t139_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ C ) =>
% 0.21/0.55       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.55         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.55         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 0.21/0.55            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.21/0.55  thf(dt_k7_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.55  thf(d10_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.55  thf('4', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.21/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.55  thf(t162_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i,C:$i]:
% 0.21/0.55         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.55           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.21/0.55             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X10 @ X11)
% 0.21/0.55          | ((k9_relat_1 @ (k7_relat_1 @ X12 @ X11) @ X10)
% 0.21/0.55              = (k9_relat_1 @ X12 @ X10))
% 0.21/0.55          | ~ (v1_relat_1 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.21/0.55              = (k9_relat_1 @ X1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf(t169_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X13 : $i]:
% 0.21/0.55         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 0.21/0.55          | ~ (v1_relat_1 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.55  thf('8', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t71_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.55  thf('9', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf(t97_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.55         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 0.21/0.55          | ((k7_relat_1 @ X18 @ X19) = (X18))
% 0.21/0.55          | ~ (v1_relat_1 @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.55          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf(fc3_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.55  thf('12', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.21/0.55         = (k6_relat_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.55         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 0.21/0.55            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 0.21/0.55            = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.21/0.55               (k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 0.21/0.55           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.21/0.55              (k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf(t90_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.21/0.55         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 0.21/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 0.21/0.55          | ~ (v1_relat_1 @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.55  thf(t146_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X9 : $i]:
% 0.21/0.55         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 0.21/0.55          | ~ (v1_relat_1 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.55            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.55            = (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.55              (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.55              = (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.21/0.55      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k9_relat_1 @ 
% 0.21/0.55            (k7_relat_1 @ sk_B @ (k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0)) @ 
% 0.21/0.55            (k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0))
% 0.21/0.55            = (k2_relat_1 @ 
% 0.21/0.55               (k7_relat_1 @ sk_B @ (k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0))))
% 0.21/0.55          | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['18', '23'])).
% 0.21/0.55  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k9_relat_1 @ 
% 0.21/0.55           (k7_relat_1 @ sk_B @ (k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0)) @ 
% 0.21/0.55           (k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0))
% 0.21/0.55           = (k2_relat_1 @ 
% 0.21/0.55              (k7_relat_1 @ sk_B @ (k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      ((((k9_relat_1 @ 
% 0.21/0.55          (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A))) @ 
% 0.21/0.55          (k10_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.21/0.55           (k2_relat_1 @ (k6_relat_1 @ sk_A))))
% 0.21/0.55          = (k2_relat_1 @ 
% 0.21/0.55             (k7_relat_1 @ sk_B @ 
% 0.21/0.55              (k10_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.21/0.55               (k2_relat_1 @ (k6_relat_1 @ sk_A))))))
% 0.21/0.55        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['7', '26'])).
% 0.21/0.55  thf('28', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf('29', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf('30', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X13 : $i]:
% 0.21/0.55         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 0.21/0.55          | ~ (v1_relat_1 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.21/0.55            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf('33', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf('34', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.55  thf('36', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.55  thf('38', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.55         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)],
% 0.21/0.55                ['27', '28', '29', '35', '36', '37', '38'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['6', '39'])).
% 0.21/0.55  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X13 : $i]:
% 0.21/0.55         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 0.21/0.55          | ~ (v1_relat_1 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.55          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['42', '43'])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.55        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.21/0.55            (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.55            = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '44'])).
% 0.21/0.55  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.55         = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      ((((k3_xboole_0 @ sk_A @ 
% 0.21/0.55          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['1', '47'])).
% 0.21/0.55  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55         = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 0.21/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 0.21/0.55          | ~ (v1_relat_1 @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55         = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.55  thf(t17_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.21/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (![X2 : $i, X4 : $i]:
% 0.21/0.55         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.21/0.55          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55        | ((sk_A)
% 0.21/0.55            = (k3_xboole_0 @ sk_A @ 
% 0.21/0.55               (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['52', '55'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55         = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55        | ((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.55        | ((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['51', '58'])).
% 0.21/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.21/0.55         = (k6_relat_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 0.21/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 0.21/0.55          | ~ (v1_relat_1 @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      ((((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.21/0.55          = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ 
% 0.21/0.55             (k1_relat_1 @ sk_B)))
% 0.21/0.55        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.21/0.55  thf('64', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf('65', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf('66', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('67', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.21/0.55  thf('68', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.21/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.55  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('70', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['59', '60', '67', '68', '69'])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.55         = (sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['50', '70'])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.21/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.55  thf('74', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.55      inference('sup+', [status(thm)], ['72', '73'])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['71', '74'])).
% 0.21/0.55  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
