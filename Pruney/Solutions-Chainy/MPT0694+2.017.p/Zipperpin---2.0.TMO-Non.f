%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.38OgFCO4lv

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:34 EST 2020

% Result     : Timeout 59.01s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  111 ( 255 expanded)
%              Number of leaves         :   22 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          : 1087 (2237 expanded)
%              Number of equality atoms :   40 ( 145 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) @ X8 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ X42 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( r1_tarski @ ( k9_relat_1 @ X44 @ X42 ) @ ( k9_relat_1 @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('8',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) @ X8 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('23',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X45 @ ( k10_relat_1 @ X45 @ X46 ) ) @ X46 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k3_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('25',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X7 ) ) @ X6 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X2 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ X0 ) ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('31',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ X42 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( r1_tarski @ ( k9_relat_1 @ X44 @ X42 ) @ ( k9_relat_1 @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X3 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k10_relat_1 @ X2 @ X0 ) ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) @ X8 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) @ X8 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('69',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
      = ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['44','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['43','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k10_relat_1 @ X2 @ X0 ) ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k9_relat_1 @ X2 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k10_relat_1 @ X2 @ X0 ) ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k9_relat_1 @ X2 @ X1 ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['76'])).

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

thf('78',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('80',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('81',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('83',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['84','85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.38OgFCO4lv
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 59.01/59.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 59.01/59.19  % Solved by: fo/fo7.sh
% 59.01/59.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 59.01/59.19  % done 24965 iterations in 58.734s
% 59.01/59.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 59.01/59.19  % SZS output start Refutation
% 59.01/59.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 59.01/59.19  thf(sk_B_type, type, sk_B: $i).
% 59.01/59.19  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 59.01/59.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 59.01/59.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 59.01/59.19  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 59.01/59.19  thf(sk_A_type, type, sk_A: $i).
% 59.01/59.19  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 59.01/59.19  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 59.01/59.19  thf(sk_C_type, type, sk_C: $i).
% 59.01/59.19  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 59.01/59.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 59.01/59.19  thf(t17_xboole_1, axiom,
% 59.01/59.19    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 59.01/59.19  thf('0', plain,
% 59.01/59.19      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 59.01/59.19      inference('cnf', [status(esa)], [t17_xboole_1])).
% 59.01/59.19  thf(t12_setfam_1, axiom,
% 59.01/59.19    (![A:$i,B:$i]:
% 59.01/59.19     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 59.01/59.19  thf('1', plain,
% 59.01/59.19      (![X40 : $i, X41 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 59.01/59.19      inference('cnf', [status(esa)], [t12_setfam_1])).
% 59.01/59.19  thf('2', plain,
% 59.01/59.19      (![X8 : $i, X9 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)) @ X8)),
% 59.01/59.19      inference('demod', [status(thm)], ['0', '1'])).
% 59.01/59.19  thf(t156_relat_1, axiom,
% 59.01/59.19    (![A:$i,B:$i,C:$i]:
% 59.01/59.19     ( ( v1_relat_1 @ C ) =>
% 59.01/59.19       ( ( r1_tarski @ A @ B ) =>
% 59.01/59.19         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 59.01/59.19  thf('3', plain,
% 59.01/59.19      (![X42 : $i, X43 : $i, X44 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X42 @ X43)
% 59.01/59.19          | ~ (v1_relat_1 @ X44)
% 59.01/59.19          | (r1_tarski @ (k9_relat_1 @ X44 @ X42) @ (k9_relat_1 @ X44 @ X43)))),
% 59.01/59.19      inference('cnf', [status(esa)], [t156_relat_1])).
% 59.01/59.19  thf('4', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         ((r1_tarski @ 
% 59.01/59.19           (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 59.01/59.19           (k9_relat_1 @ X2 @ X0))
% 59.01/59.19          | ~ (v1_relat_1 @ X2))),
% 59.01/59.19      inference('sup-', [status(thm)], ['2', '3'])).
% 59.01/59.19  thf(d10_xboole_0, axiom,
% 59.01/59.19    (![A:$i,B:$i]:
% 59.01/59.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 59.01/59.19  thf('5', plain,
% 59.01/59.19      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 59.01/59.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 59.01/59.19  thf('6', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 59.01/59.19      inference('simplify', [status(thm)], ['5'])).
% 59.01/59.19  thf(t19_xboole_1, axiom,
% 59.01/59.19    (![A:$i,B:$i,C:$i]:
% 59.01/59.19     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 59.01/59.19       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 59.01/59.19  thf('7', plain,
% 59.01/59.19      (![X10 : $i, X11 : $i, X12 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X10 @ X11)
% 59.01/59.19          | ~ (r1_tarski @ X10 @ X12)
% 59.01/59.19          | (r1_tarski @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 59.01/59.19      inference('cnf', [status(esa)], [t19_xboole_1])).
% 59.01/59.19  thf('8', plain,
% 59.01/59.19      (![X40 : $i, X41 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 59.01/59.19      inference('cnf', [status(esa)], [t12_setfam_1])).
% 59.01/59.19  thf('9', plain,
% 59.01/59.19      (![X10 : $i, X11 : $i, X12 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X10 @ X11)
% 59.01/59.19          | ~ (r1_tarski @ X10 @ X12)
% 59.01/59.19          | (r1_tarski @ X10 @ (k1_setfam_1 @ (k2_tarski @ X11 @ X12))))),
% 59.01/59.19      inference('demod', [status(thm)], ['7', '8'])).
% 59.01/59.19  thf('10', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 59.01/59.19          | ~ (r1_tarski @ X0 @ X1))),
% 59.01/59.19      inference('sup-', [status(thm)], ['6', '9'])).
% 59.01/59.19  thf('11', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         (~ (v1_relat_1 @ X1)
% 59.01/59.19          | (r1_tarski @ 
% 59.01/59.19             (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 59.01/59.19             (k1_setfam_1 @ 
% 59.01/59.19              (k2_tarski @ 
% 59.01/59.19               (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 59.01/59.19               (k9_relat_1 @ X1 @ X0)))))),
% 59.01/59.19      inference('sup-', [status(thm)], ['4', '10'])).
% 59.01/59.19  thf(commutativity_k3_xboole_0, axiom,
% 59.01/59.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 59.01/59.19  thf('12', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.01/59.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.01/59.19  thf('13', plain,
% 59.01/59.19      (![X40 : $i, X41 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 59.01/59.19      inference('cnf', [status(esa)], [t12_setfam_1])).
% 59.01/59.19  thf('14', plain,
% 59.01/59.19      (![X40 : $i, X41 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 59.01/59.19      inference('cnf', [status(esa)], [t12_setfam_1])).
% 59.01/59.19  thf('15', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 59.01/59.19           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 59.01/59.19      inference('demod', [status(thm)], ['12', '13', '14'])).
% 59.01/59.19  thf('16', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         (~ (v1_relat_1 @ X1)
% 59.01/59.19          | (r1_tarski @ 
% 59.01/59.19             (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 59.01/59.19             (k1_setfam_1 @ 
% 59.01/59.19              (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ 
% 59.01/59.19               (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2)))))))),
% 59.01/59.19      inference('demod', [status(thm)], ['11', '15'])).
% 59.01/59.19  thf('17', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 59.01/59.19           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 59.01/59.19      inference('demod', [status(thm)], ['12', '13', '14'])).
% 59.01/59.19  thf('18', plain,
% 59.01/59.19      (![X8 : $i, X9 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)) @ X8)),
% 59.01/59.19      inference('demod', [status(thm)], ['0', '1'])).
% 59.01/59.19  thf('19', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 59.01/59.19      inference('sup+', [status(thm)], ['17', '18'])).
% 59.01/59.19  thf('20', plain,
% 59.01/59.19      (![X2 : $i, X4 : $i]:
% 59.01/59.19         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 59.01/59.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 59.01/59.19  thf('21', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 59.01/59.19          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 59.01/59.19      inference('sup-', [status(thm)], ['19', '20'])).
% 59.01/59.19  thf('22', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         (~ (v1_relat_1 @ X2)
% 59.01/59.19          | ((k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 59.01/59.19              = (k1_setfam_1 @ 
% 59.01/59.19                 (k2_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 59.01/59.19                  (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))))),
% 59.01/59.19      inference('sup-', [status(thm)], ['16', '21'])).
% 59.01/59.19  thf(t145_funct_1, axiom,
% 59.01/59.19    (![A:$i,B:$i]:
% 59.01/59.19     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 59.01/59.19       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 59.01/59.19  thf('23', plain,
% 59.01/59.19      (![X45 : $i, X46 : $i]:
% 59.01/59.19         ((r1_tarski @ (k9_relat_1 @ X45 @ (k10_relat_1 @ X45 @ X46)) @ X46)
% 59.01/59.19          | ~ (v1_funct_1 @ X45)
% 59.01/59.19          | ~ (v1_relat_1 @ X45))),
% 59.01/59.19      inference('cnf', [status(esa)], [t145_funct_1])).
% 59.01/59.19  thf(t108_xboole_1, axiom,
% 59.01/59.19    (![A:$i,B:$i,C:$i]:
% 59.01/59.19     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 59.01/59.19  thf('24', plain,
% 59.01/59.19      (![X5 : $i, X6 : $i, X7 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 59.01/59.19      inference('cnf', [status(esa)], [t108_xboole_1])).
% 59.01/59.19  thf('25', plain,
% 59.01/59.19      (![X40 : $i, X41 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 59.01/59.19      inference('cnf', [status(esa)], [t12_setfam_1])).
% 59.01/59.19  thf('26', plain,
% 59.01/59.19      (![X5 : $i, X6 : $i, X7 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X5 @ X6)
% 59.01/59.19          | (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X5 @ X7)) @ X6))),
% 59.01/59.19      inference('demod', [status(thm)], ['24', '25'])).
% 59.01/59.19  thf('27', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         (~ (v1_relat_1 @ X1)
% 59.01/59.19          | ~ (v1_funct_1 @ X1)
% 59.01/59.19          | (r1_tarski @ 
% 59.01/59.19             (k1_setfam_1 @ 
% 59.01/59.19              (k2_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X2)) @ 
% 59.01/59.19             X0))),
% 59.01/59.19      inference('sup-', [status(thm)], ['23', '26'])).
% 59.01/59.19  thf('28', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         ((r1_tarski @ 
% 59.01/59.19           (k9_relat_1 @ X2 @ 
% 59.01/59.19            (k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X2 @ X1) @ X0))) @ 
% 59.01/59.19           X1)
% 59.01/59.19          | ~ (v1_relat_1 @ X2)
% 59.01/59.19          | ~ (v1_funct_1 @ X2)
% 59.01/59.19          | ~ (v1_relat_1 @ X2))),
% 59.01/59.19      inference('sup+', [status(thm)], ['22', '27'])).
% 59.01/59.19  thf('29', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         (~ (v1_funct_1 @ X2)
% 59.01/59.19          | ~ (v1_relat_1 @ X2)
% 59.01/59.19          | (r1_tarski @ 
% 59.01/59.19             (k9_relat_1 @ X2 @ 
% 59.01/59.19              (k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X2 @ X1) @ X0))) @ 
% 59.01/59.19             X1))),
% 59.01/59.19      inference('simplify', [status(thm)], ['28'])).
% 59.01/59.19  thf('30', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 59.01/59.19      inference('sup+', [status(thm)], ['17', '18'])).
% 59.01/59.19  thf('31', plain,
% 59.01/59.19      (![X42 : $i, X43 : $i, X44 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X42 @ X43)
% 59.01/59.19          | ~ (v1_relat_1 @ X44)
% 59.01/59.19          | (r1_tarski @ (k9_relat_1 @ X44 @ X42) @ (k9_relat_1 @ X44 @ X43)))),
% 59.01/59.19      inference('cnf', [status(esa)], [t156_relat_1])).
% 59.01/59.19  thf('32', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         ((r1_tarski @ 
% 59.01/59.19           (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 59.01/59.19           (k9_relat_1 @ X2 @ X0))
% 59.01/59.19          | ~ (v1_relat_1 @ X2))),
% 59.01/59.19      inference('sup-', [status(thm)], ['30', '31'])).
% 59.01/59.19  thf('33', plain,
% 59.01/59.19      (![X10 : $i, X11 : $i, X12 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X10 @ X11)
% 59.01/59.19          | ~ (r1_tarski @ X10 @ X12)
% 59.01/59.19          | (r1_tarski @ X10 @ (k1_setfam_1 @ (k2_tarski @ X11 @ X12))))),
% 59.01/59.19      inference('demod', [status(thm)], ['7', '8'])).
% 59.01/59.19  thf('34', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 59.01/59.19         (~ (v1_relat_1 @ X1)
% 59.01/59.19          | (r1_tarski @ 
% 59.01/59.19             (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 59.01/59.19             (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ X3)))
% 59.01/59.19          | ~ (r1_tarski @ 
% 59.01/59.19               (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ X3))),
% 59.01/59.19      inference('sup-', [status(thm)], ['32', '33'])).
% 59.01/59.19  thf('35', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         (~ (v1_relat_1 @ X2)
% 59.01/59.19          | ~ (v1_funct_1 @ X2)
% 59.01/59.19          | (r1_tarski @ 
% 59.01/59.19             (k9_relat_1 @ X2 @ 
% 59.01/59.19              (k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X2 @ X0) @ X1))) @ 
% 59.01/59.19             (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X2 @ X1) @ X0)))
% 59.01/59.19          | ~ (v1_relat_1 @ X2))),
% 59.01/59.19      inference('sup-', [status(thm)], ['29', '34'])).
% 59.01/59.19  thf('36', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         ((r1_tarski @ 
% 59.01/59.19           (k9_relat_1 @ X2 @ 
% 59.01/59.19            (k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X2 @ X0) @ X1))) @ 
% 59.01/59.19           (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X2 @ X1) @ X0)))
% 59.01/59.19          | ~ (v1_funct_1 @ X2)
% 59.01/59.19          | ~ (v1_relat_1 @ X2))),
% 59.01/59.19      inference('simplify', [status(thm)], ['35'])).
% 59.01/59.19  thf('37', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 59.01/59.19           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 59.01/59.19      inference('demod', [status(thm)], ['12', '13', '14'])).
% 59.01/59.19  thf('38', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         ((r1_tarski @ 
% 59.01/59.19           (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 59.01/59.19           (k9_relat_1 @ X2 @ X0))
% 59.01/59.19          | ~ (v1_relat_1 @ X2))),
% 59.01/59.19      inference('sup-', [status(thm)], ['2', '3'])).
% 59.01/59.19  thf('39', plain,
% 59.01/59.19      (![X10 : $i, X11 : $i, X12 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X10 @ X11)
% 59.01/59.19          | ~ (r1_tarski @ X10 @ X12)
% 59.01/59.19          | (r1_tarski @ X10 @ (k1_setfam_1 @ (k2_tarski @ X11 @ X12))))),
% 59.01/59.19      inference('demod', [status(thm)], ['7', '8'])).
% 59.01/59.19  thf('40', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 59.01/59.19         (~ (v1_relat_1 @ X1)
% 59.01/59.19          | (r1_tarski @ 
% 59.01/59.19             (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 59.01/59.19             (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ X3)))
% 59.01/59.19          | ~ (r1_tarski @ 
% 59.01/59.19               (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 59.01/59.19      inference('sup-', [status(thm)], ['38', '39'])).
% 59.01/59.19  thf('41', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 59.01/59.19         (~ (r1_tarski @ 
% 59.01/59.19             (k9_relat_1 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ X2)
% 59.01/59.19          | (r1_tarski @ 
% 59.01/59.19             (k9_relat_1 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 59.01/59.19             (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X3 @ X0) @ X2)))
% 59.01/59.19          | ~ (v1_relat_1 @ X3))),
% 59.01/59.19      inference('sup-', [status(thm)], ['37', '40'])).
% 59.01/59.19  thf('42', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         (~ (v1_relat_1 @ X2)
% 59.01/59.19          | ~ (v1_funct_1 @ X2)
% 59.01/59.19          | ~ (v1_relat_1 @ X2)
% 59.01/59.19          | (r1_tarski @ 
% 59.01/59.19             (k9_relat_1 @ X2 @ 
% 59.01/59.19              (k1_setfam_1 @ (k2_tarski @ X1 @ (k10_relat_1 @ X2 @ X0)))) @ 
% 59.01/59.19             (k1_setfam_1 @ 
% 59.01/59.19              (k2_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 59.01/59.19               (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X2 @ X1) @ X0))))))),
% 59.01/59.19      inference('sup-', [status(thm)], ['36', '41'])).
% 59.01/59.19  thf('43', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 59.01/59.19           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 59.01/59.19      inference('demod', [status(thm)], ['12', '13', '14'])).
% 59.01/59.19  thf(t70_enumset1, axiom,
% 59.01/59.19    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 59.01/59.19  thf('44', plain,
% 59.01/59.19      (![X13 : $i, X14 : $i]:
% 59.01/59.19         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 59.01/59.19      inference('cnf', [status(esa)], [t70_enumset1])).
% 59.01/59.19  thf('45', plain,
% 59.01/59.19      (![X13 : $i, X14 : $i]:
% 59.01/59.19         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 59.01/59.19      inference('cnf', [status(esa)], [t70_enumset1])).
% 59.01/59.19  thf('46', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 59.01/59.19           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 59.01/59.19      inference('demod', [status(thm)], ['12', '13', '14'])).
% 59.01/59.19  thf('47', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 59.01/59.19           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 59.01/59.19      inference('sup+', [status(thm)], ['45', '46'])).
% 59.01/59.19  thf('48', plain,
% 59.01/59.19      (![X13 : $i, X14 : $i]:
% 59.01/59.19         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 59.01/59.19      inference('cnf', [status(esa)], [t70_enumset1])).
% 59.01/59.19  thf('49', plain,
% 59.01/59.19      (![X8 : $i, X9 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)) @ X8)),
% 59.01/59.19      inference('demod', [status(thm)], ['0', '1'])).
% 59.01/59.19  thf('50', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)) @ X1)),
% 59.01/59.19      inference('sup+', [status(thm)], ['48', '49'])).
% 59.01/59.19  thf('51', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 59.01/59.19          | ~ (r1_tarski @ X0 @ X1))),
% 59.01/59.19      inference('sup-', [status(thm)], ['6', '9'])).
% 59.01/59.19  thf('52', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ X1)) @ 
% 59.01/59.19          (k1_setfam_1 @ 
% 59.01/59.19           (k2_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ X1)) @ X0)))),
% 59.01/59.19      inference('sup-', [status(thm)], ['50', '51'])).
% 59.01/59.19  thf('53', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 59.01/59.19           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 59.01/59.19      inference('demod', [status(thm)], ['12', '13', '14'])).
% 59.01/59.19  thf('54', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ X1)) @ 
% 59.01/59.19          (k1_setfam_1 @ 
% 59.01/59.19           (k2_tarski @ X0 @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ X1)))))),
% 59.01/59.19      inference('demod', [status(thm)], ['52', '53'])).
% 59.01/59.19  thf('55', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 59.01/59.19          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 59.01/59.19      inference('sup-', [status(thm)], ['19', '20'])).
% 59.01/59.19  thf('56', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 59.01/59.19           = (k1_setfam_1 @ 
% 59.01/59.19              (k2_tarski @ X1 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)))))),
% 59.01/59.19      inference('sup-', [status(thm)], ['54', '55'])).
% 59.01/59.19  thf('57', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ X1))
% 59.01/59.19           = (k1_setfam_1 @ 
% 59.01/59.19              (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 59.01/59.19      inference('sup+', [status(thm)], ['47', '56'])).
% 59.01/59.19  thf('58', plain,
% 59.01/59.19      (![X13 : $i, X14 : $i]:
% 59.01/59.19         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 59.01/59.19      inference('cnf', [status(esa)], [t70_enumset1])).
% 59.01/59.19  thf('59', plain,
% 59.01/59.19      (![X13 : $i, X14 : $i]:
% 59.01/59.19         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 59.01/59.19      inference('cnf', [status(esa)], [t70_enumset1])).
% 59.01/59.19  thf('60', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 59.01/59.19      inference('sup+', [status(thm)], ['17', '18'])).
% 59.01/59.19  thf('61', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)) @ X0)),
% 59.01/59.19      inference('sup+', [status(thm)], ['59', '60'])).
% 59.01/59.19  thf('62', plain,
% 59.01/59.19      (![X2 : $i, X4 : $i]:
% 59.01/59.19         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 59.01/59.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 59.01/59.19  thf('63', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)))
% 59.01/59.19          | ((X0) = (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))))),
% 59.01/59.19      inference('sup-', [status(thm)], ['61', '62'])).
% 59.01/59.19  thf('64', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 59.01/59.19          | ((X0) = (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))))),
% 59.01/59.19      inference('sup-', [status(thm)], ['58', '63'])).
% 59.01/59.19  thf('65', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 59.01/59.19             (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)))
% 59.01/59.19          | ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 59.01/59.19              = (k1_setfam_1 @ 
% 59.01/59.19                 (k1_enumset1 @ X1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))))),
% 59.01/59.19      inference('sup-', [status(thm)], ['57', '64'])).
% 59.01/59.19  thf('66', plain,
% 59.01/59.19      (![X13 : $i, X14 : $i]:
% 59.01/59.19         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 59.01/59.19      inference('cnf', [status(esa)], [t70_enumset1])).
% 59.01/59.19  thf('67', plain,
% 59.01/59.19      (![X8 : $i, X9 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)) @ X8)),
% 59.01/59.19      inference('demod', [status(thm)], ['0', '1'])).
% 59.01/59.19  thf('68', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 59.01/59.19      inference('sup+', [status(thm)], ['17', '18'])).
% 59.01/59.19  thf('69', plain,
% 59.01/59.19      (![X10 : $i, X11 : $i, X12 : $i]:
% 59.01/59.19         (~ (r1_tarski @ X10 @ X11)
% 59.01/59.19          | ~ (r1_tarski @ X10 @ X12)
% 59.01/59.19          | (r1_tarski @ X10 @ (k1_setfam_1 @ (k2_tarski @ X11 @ X12))))),
% 59.01/59.19      inference('demod', [status(thm)], ['7', '8'])).
% 59.01/59.19  thf('70', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 59.01/59.19           (k1_setfam_1 @ (k2_tarski @ X0 @ X2)))
% 59.01/59.19          | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2))),
% 59.01/59.19      inference('sup-', [status(thm)], ['68', '69'])).
% 59.01/59.19  thf('71', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 59.01/59.19          (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 59.01/59.19      inference('sup-', [status(thm)], ['67', '70'])).
% 59.01/59.19  thf('72', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 59.01/59.19          (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)))),
% 59.01/59.19      inference('sup+', [status(thm)], ['66', '71'])).
% 59.01/59.19  thf('73', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 59.01/59.19           = (k1_setfam_1 @ 
% 59.01/59.19              (k1_enumset1 @ X1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))))),
% 59.01/59.19      inference('demod', [status(thm)], ['65', '72'])).
% 59.01/59.19  thf('74', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 59.01/59.19           = (k1_setfam_1 @ 
% 59.01/59.19              (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 59.01/59.19      inference('sup+', [status(thm)], ['44', '73'])).
% 59.01/59.19  thf('75', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 59.01/59.19           = (k1_setfam_1 @ 
% 59.01/59.19              (k2_tarski @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 59.01/59.19      inference('sup+', [status(thm)], ['43', '74'])).
% 59.01/59.19  thf('76', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         (~ (v1_relat_1 @ X2)
% 59.01/59.19          | ~ (v1_funct_1 @ X2)
% 59.01/59.19          | ~ (v1_relat_1 @ X2)
% 59.01/59.19          | (r1_tarski @ 
% 59.01/59.19             (k9_relat_1 @ X2 @ 
% 59.01/59.19              (k1_setfam_1 @ (k2_tarski @ X1 @ (k10_relat_1 @ X2 @ X0)))) @ 
% 59.01/59.19             (k1_setfam_1 @ (k2_tarski @ X0 @ (k9_relat_1 @ X2 @ X1)))))),
% 59.01/59.19      inference('demod', [status(thm)], ['42', '75'])).
% 59.01/59.19  thf('77', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.01/59.19         ((r1_tarski @ 
% 59.01/59.19           (k9_relat_1 @ X2 @ 
% 59.01/59.19            (k1_setfam_1 @ (k2_tarski @ X1 @ (k10_relat_1 @ X2 @ X0)))) @ 
% 59.01/59.19           (k1_setfam_1 @ (k2_tarski @ X0 @ (k9_relat_1 @ X2 @ X1))))
% 59.01/59.19          | ~ (v1_funct_1 @ X2)
% 59.01/59.19          | ~ (v1_relat_1 @ X2))),
% 59.01/59.19      inference('simplify', [status(thm)], ['76'])).
% 59.01/59.19  thf(t149_funct_1, conjecture,
% 59.01/59.19    (![A:$i,B:$i,C:$i]:
% 59.01/59.19     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 59.01/59.19       ( r1_tarski @
% 59.01/59.19         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 59.01/59.19         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 59.01/59.19  thf(zf_stmt_0, negated_conjecture,
% 59.01/59.19    (~( ![A:$i,B:$i,C:$i]:
% 59.01/59.19        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 59.01/59.19          ( r1_tarski @
% 59.01/59.19            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 59.01/59.19            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 59.01/59.19    inference('cnf.neg', [status(esa)], [t149_funct_1])).
% 59.01/59.19  thf('78', plain,
% 59.01/59.19      (~ (r1_tarski @ 
% 59.01/59.19          (k9_relat_1 @ sk_C @ 
% 59.01/59.19           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 59.01/59.19          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 59.01/59.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.01/59.19  thf('79', plain,
% 59.01/59.19      (![X40 : $i, X41 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 59.01/59.19      inference('cnf', [status(esa)], [t12_setfam_1])).
% 59.01/59.19  thf('80', plain,
% 59.01/59.19      (![X40 : $i, X41 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 59.01/59.19      inference('cnf', [status(esa)], [t12_setfam_1])).
% 59.01/59.19  thf('81', plain,
% 59.01/59.19      (~ (r1_tarski @ 
% 59.01/59.19          (k9_relat_1 @ sk_C @ 
% 59.01/59.19           (k1_setfam_1 @ (k2_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))) @ 
% 59.01/59.19          (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)))),
% 59.01/59.19      inference('demod', [status(thm)], ['78', '79', '80'])).
% 59.01/59.19  thf('82', plain,
% 59.01/59.19      (![X0 : $i, X1 : $i]:
% 59.01/59.19         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 59.01/59.19           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 59.01/59.19      inference('demod', [status(thm)], ['12', '13', '14'])).
% 59.01/59.19  thf('83', plain,
% 59.01/59.19      (~ (r1_tarski @ 
% 59.01/59.19          (k9_relat_1 @ sk_C @ 
% 59.01/59.19           (k1_setfam_1 @ (k2_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))) @ 
% 59.01/59.19          (k1_setfam_1 @ (k2_tarski @ sk_B @ (k9_relat_1 @ sk_C @ sk_A))))),
% 59.01/59.19      inference('demod', [status(thm)], ['81', '82'])).
% 59.01/59.19  thf('84', plain, ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C))),
% 59.01/59.19      inference('sup-', [status(thm)], ['77', '83'])).
% 59.01/59.19  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 59.01/59.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.01/59.19  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 59.01/59.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.01/59.19  thf('87', plain, ($false),
% 59.01/59.19      inference('demod', [status(thm)], ['84', '85', '86'])).
% 59.01/59.19  
% 59.01/59.19  % SZS output end Refutation
% 59.01/59.19  
% 59.01/59.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
