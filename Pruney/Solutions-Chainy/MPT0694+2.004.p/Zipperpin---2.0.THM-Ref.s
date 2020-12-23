%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QAAlP9CZtt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:33 EST 2020

% Result     : Theorem 36.77s
% Output     : Refutation 36.77s
% Verified   : 
% Statistics : Number of formulae       :   74 (  90 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :  717 ( 881 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X44 @ X45 ) )
        = ( k9_relat_1 @ X44 @ X45 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) @ X40 )
        = ( k7_relat_1 @ X38 @ ( k3_xboole_0 @ X39 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('8',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ X41 @ X42 )
      | ~ ( v1_relat_1 @ X43 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X43 @ X42 ) @ X41 )
        = ( k7_relat_1 @ X43 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) @ X40 )
        = ( k7_relat_1 @ X38 @ ( k3_xboole_0 @ X39 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('13',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X44 @ X45 ) )
        = ( k9_relat_1 @ X44 @ X45 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('20',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X52 @ X51 ) @ X53 )
        = ( k3_xboole_0 @ X51 @ ( k10_relat_1 @ X52 @ X53 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('22',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X54 @ ( k10_relat_1 @ X54 @ X55 ) ) @ X55 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('33',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X46 @ X47 )
      | ~ ( v1_relat_1 @ X48 )
      | ( r1_tarski @ ( k9_relat_1 @ X48 @ X46 ) @ ( k9_relat_1 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','38'])).

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

thf('40',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QAAlP9CZtt
% 0.13/0.38  % Computer   : n016.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 15:52:34 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 36.77/37.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 36.77/37.03  % Solved by: fo/fo7.sh
% 36.77/37.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.77/37.03  % done 8585 iterations in 36.532s
% 36.77/37.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 36.77/37.03  % SZS output start Refutation
% 36.77/37.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 36.77/37.03  thf(sk_C_type, type, sk_C: $i).
% 36.77/37.03  thf(sk_B_type, type, sk_B: $i).
% 36.77/37.03  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 36.77/37.03  thf(sk_A_type, type, sk_A: $i).
% 36.77/37.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 36.77/37.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 36.77/37.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 36.77/37.03  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 36.77/37.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 36.77/37.03  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 36.77/37.03  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 36.77/37.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 36.77/37.03  thf(commutativity_k2_tarski, axiom,
% 36.77/37.03    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 36.77/37.03  thf('0', plain,
% 36.77/37.03      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 36.77/37.03      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 36.77/37.03  thf(t12_setfam_1, axiom,
% 36.77/37.03    (![A:$i,B:$i]:
% 36.77/37.03     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 36.77/37.03  thf('1', plain,
% 36.77/37.03      (![X34 : $i, X35 : $i]:
% 36.77/37.03         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 36.77/37.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 36.77/37.03  thf('2', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i]:
% 36.77/37.03         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 36.77/37.03      inference('sup+', [status(thm)], ['0', '1'])).
% 36.77/37.03  thf('3', plain,
% 36.77/37.03      (![X34 : $i, X35 : $i]:
% 36.77/37.03         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 36.77/37.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 36.77/37.03  thf('4', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 36.77/37.03      inference('sup+', [status(thm)], ['2', '3'])).
% 36.77/37.03  thf(t148_relat_1, axiom,
% 36.77/37.03    (![A:$i,B:$i]:
% 36.77/37.03     ( ( v1_relat_1 @ B ) =>
% 36.77/37.03       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 36.77/37.03  thf('5', plain,
% 36.77/37.03      (![X44 : $i, X45 : $i]:
% 36.77/37.03         (((k2_relat_1 @ (k7_relat_1 @ X44 @ X45)) = (k9_relat_1 @ X44 @ X45))
% 36.77/37.03          | ~ (v1_relat_1 @ X44))),
% 36.77/37.03      inference('cnf', [status(esa)], [t148_relat_1])).
% 36.77/37.03  thf(t100_relat_1, axiom,
% 36.77/37.03    (![A:$i,B:$i,C:$i]:
% 36.77/37.03     ( ( v1_relat_1 @ C ) =>
% 36.77/37.03       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 36.77/37.03         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 36.77/37.03  thf('6', plain,
% 36.77/37.03      (![X38 : $i, X39 : $i, X40 : $i]:
% 36.77/37.03         (((k7_relat_1 @ (k7_relat_1 @ X38 @ X39) @ X40)
% 36.77/37.03            = (k7_relat_1 @ X38 @ (k3_xboole_0 @ X39 @ X40)))
% 36.77/37.03          | ~ (v1_relat_1 @ X38))),
% 36.77/37.03      inference('cnf', [status(esa)], [t100_relat_1])).
% 36.77/37.03  thf(t17_xboole_1, axiom,
% 36.77/37.03    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 36.77/37.03  thf('7', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 36.77/37.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 36.77/37.03  thf(t103_relat_1, axiom,
% 36.77/37.03    (![A:$i,B:$i,C:$i]:
% 36.77/37.03     ( ( v1_relat_1 @ C ) =>
% 36.77/37.03       ( ( r1_tarski @ A @ B ) =>
% 36.77/37.03         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 36.77/37.03  thf('8', plain,
% 36.77/37.03      (![X41 : $i, X42 : $i, X43 : $i]:
% 36.77/37.03         (~ (r1_tarski @ X41 @ X42)
% 36.77/37.03          | ~ (v1_relat_1 @ X43)
% 36.77/37.03          | ((k7_relat_1 @ (k7_relat_1 @ X43 @ X42) @ X41)
% 36.77/37.03              = (k7_relat_1 @ X43 @ X41)))),
% 36.77/37.03      inference('cnf', [status(esa)], [t103_relat_1])).
% 36.77/37.03  thf('9', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 36.77/37.03            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 36.77/37.03          | ~ (v1_relat_1 @ X2))),
% 36.77/37.03      inference('sup-', [status(thm)], ['7', '8'])).
% 36.77/37.03  thf('10', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (((k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 36.77/37.03            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 36.77/37.03          | ~ (v1_relat_1 @ X2)
% 36.77/37.03          | ~ (v1_relat_1 @ X2))),
% 36.77/37.03      inference('sup+', [status(thm)], ['6', '9'])).
% 36.77/37.03  thf('11', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (~ (v1_relat_1 @ X2)
% 36.77/37.03          | ((k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 36.77/37.03              = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 36.77/37.03      inference('simplify', [status(thm)], ['10'])).
% 36.77/37.03  thf('12', plain,
% 36.77/37.03      (![X38 : $i, X39 : $i, X40 : $i]:
% 36.77/37.03         (((k7_relat_1 @ (k7_relat_1 @ X38 @ X39) @ X40)
% 36.77/37.03            = (k7_relat_1 @ X38 @ (k3_xboole_0 @ X39 @ X40)))
% 36.77/37.03          | ~ (v1_relat_1 @ X38))),
% 36.77/37.03      inference('cnf', [status(esa)], [t100_relat_1])).
% 36.77/37.03  thf('13', plain,
% 36.77/37.03      (![X44 : $i, X45 : $i]:
% 36.77/37.03         (((k2_relat_1 @ (k7_relat_1 @ X44 @ X45)) = (k9_relat_1 @ X44 @ X45))
% 36.77/37.03          | ~ (v1_relat_1 @ X44))),
% 36.77/37.03      inference('cnf', [status(esa)], [t148_relat_1])).
% 36.77/37.03  thf('14', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 36.77/37.03            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 36.77/37.03          | ~ (v1_relat_1 @ X2)
% 36.77/37.03          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 36.77/37.03      inference('sup+', [status(thm)], ['12', '13'])).
% 36.77/37.03  thf(dt_k7_relat_1, axiom,
% 36.77/37.03    (![A:$i,B:$i]:
% 36.77/37.03     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 36.77/37.03  thf('15', plain,
% 36.77/37.03      (![X36 : $i, X37 : $i]:
% 36.77/37.03         (~ (v1_relat_1 @ X36) | (v1_relat_1 @ (k7_relat_1 @ X36 @ X37)))),
% 36.77/37.03      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 36.77/37.03  thf('16', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (~ (v1_relat_1 @ X2)
% 36.77/37.03          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 36.77/37.03              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 36.77/37.03      inference('clc', [status(thm)], ['14', '15'])).
% 36.77/37.03  thf('17', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 36.77/37.03            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 36.77/37.03          | ~ (v1_relat_1 @ X2)
% 36.77/37.03          | ~ (v1_relat_1 @ X2))),
% 36.77/37.03      inference('sup+', [status(thm)], ['11', '16'])).
% 36.77/37.03  thf('18', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (~ (v1_relat_1 @ X2)
% 36.77/37.03          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 36.77/37.03              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0))))),
% 36.77/37.03      inference('simplify', [status(thm)], ['17'])).
% 36.77/37.03  thf(fc8_funct_1, axiom,
% 36.77/37.03    (![A:$i,B:$i]:
% 36.77/37.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 36.77/37.03       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 36.77/37.03         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 36.77/37.03  thf('19', plain,
% 36.77/37.03      (![X49 : $i, X50 : $i]:
% 36.77/37.03         (~ (v1_funct_1 @ X49)
% 36.77/37.03          | ~ (v1_relat_1 @ X49)
% 36.77/37.03          | (v1_funct_1 @ (k7_relat_1 @ X49 @ X50)))),
% 36.77/37.03      inference('cnf', [status(esa)], [fc8_funct_1])).
% 36.77/37.03  thf('20', plain,
% 36.77/37.03      (![X36 : $i, X37 : $i]:
% 36.77/37.03         (~ (v1_relat_1 @ X36) | (v1_relat_1 @ (k7_relat_1 @ X36 @ X37)))),
% 36.77/37.03      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 36.77/37.03  thf(t139_funct_1, axiom,
% 36.77/37.03    (![A:$i,B:$i,C:$i]:
% 36.77/37.03     ( ( v1_relat_1 @ C ) =>
% 36.77/37.03       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 36.77/37.03         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 36.77/37.03  thf('21', plain,
% 36.77/37.03      (![X51 : $i, X52 : $i, X53 : $i]:
% 36.77/37.03         (((k10_relat_1 @ (k7_relat_1 @ X52 @ X51) @ X53)
% 36.77/37.03            = (k3_xboole_0 @ X51 @ (k10_relat_1 @ X52 @ X53)))
% 36.77/37.03          | ~ (v1_relat_1 @ X52))),
% 36.77/37.03      inference('cnf', [status(esa)], [t139_funct_1])).
% 36.77/37.03  thf(t145_funct_1, axiom,
% 36.77/37.03    (![A:$i,B:$i]:
% 36.77/37.03     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 36.77/37.03       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 36.77/37.03  thf('22', plain,
% 36.77/37.03      (![X54 : $i, X55 : $i]:
% 36.77/37.03         ((r1_tarski @ (k9_relat_1 @ X54 @ (k10_relat_1 @ X54 @ X55)) @ X55)
% 36.77/37.03          | ~ (v1_funct_1 @ X54)
% 36.77/37.03          | ~ (v1_relat_1 @ X54))),
% 36.77/37.03      inference('cnf', [status(esa)], [t145_funct_1])).
% 36.77/37.03  thf('23', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         ((r1_tarski @ 
% 36.77/37.03           (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 36.77/37.03            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 36.77/37.03           X0)
% 36.77/37.03          | ~ (v1_relat_1 @ X1)
% 36.77/37.03          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2))
% 36.77/37.03          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X2)))),
% 36.77/37.03      inference('sup+', [status(thm)], ['21', '22'])).
% 36.77/37.03  thf('24', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (~ (v1_relat_1 @ X1)
% 36.77/37.03          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 36.77/37.03          | ~ (v1_relat_1 @ X1)
% 36.77/37.03          | (r1_tarski @ 
% 36.77/37.03             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 36.77/37.03              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 36.77/37.03             X2))),
% 36.77/37.03      inference('sup-', [status(thm)], ['20', '23'])).
% 36.77/37.03  thf('25', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         ((r1_tarski @ 
% 36.77/37.03           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 36.77/37.03            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 36.77/37.03           X2)
% 36.77/37.03          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 36.77/37.03          | ~ (v1_relat_1 @ X1))),
% 36.77/37.03      inference('simplify', [status(thm)], ['24'])).
% 36.77/37.03  thf('26', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (~ (v1_relat_1 @ X1)
% 36.77/37.03          | ~ (v1_funct_1 @ X1)
% 36.77/37.03          | ~ (v1_relat_1 @ X1)
% 36.77/37.03          | (r1_tarski @ 
% 36.77/37.03             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 36.77/37.03              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 36.77/37.03             X2))),
% 36.77/37.03      inference('sup-', [status(thm)], ['19', '25'])).
% 36.77/37.03  thf('27', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         ((r1_tarski @ 
% 36.77/37.03           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 36.77/37.03            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 36.77/37.03           X2)
% 36.77/37.03          | ~ (v1_funct_1 @ X1)
% 36.77/37.03          | ~ (v1_relat_1 @ X1))),
% 36.77/37.03      inference('simplify', [status(thm)], ['26'])).
% 36.77/37.03  thf('28', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         ((r1_tarski @ 
% 36.77/37.03           (k2_relat_1 @ 
% 36.77/37.03            (k7_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 36.77/37.03           X0)
% 36.77/37.03          | ~ (v1_relat_1 @ X1)
% 36.77/37.03          | ~ (v1_relat_1 @ X1)
% 36.77/37.03          | ~ (v1_funct_1 @ X1))),
% 36.77/37.03      inference('sup+', [status(thm)], ['18', '27'])).
% 36.77/37.03  thf('29', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (~ (v1_funct_1 @ X1)
% 36.77/37.03          | ~ (v1_relat_1 @ X1)
% 36.77/37.03          | (r1_tarski @ 
% 36.77/37.03             (k2_relat_1 @ 
% 36.77/37.03              (k7_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 36.77/37.03             X0))),
% 36.77/37.03      inference('simplify', [status(thm)], ['28'])).
% 36.77/37.03  thf('30', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         ((r1_tarski @ 
% 36.77/37.03           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 36.77/37.03           X0)
% 36.77/37.03          | ~ (v1_relat_1 @ X1)
% 36.77/37.03          | ~ (v1_relat_1 @ X1)
% 36.77/37.03          | ~ (v1_funct_1 @ X1))),
% 36.77/37.03      inference('sup+', [status(thm)], ['5', '29'])).
% 36.77/37.03  thf('31', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (~ (v1_funct_1 @ X1)
% 36.77/37.03          | ~ (v1_relat_1 @ X1)
% 36.77/37.03          | (r1_tarski @ 
% 36.77/37.03             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 36.77/37.03             X0))),
% 36.77/37.03      inference('simplify', [status(thm)], ['30'])).
% 36.77/37.03  thf('32', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 36.77/37.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 36.77/37.03  thf(t156_relat_1, axiom,
% 36.77/37.03    (![A:$i,B:$i,C:$i]:
% 36.77/37.03     ( ( v1_relat_1 @ C ) =>
% 36.77/37.03       ( ( r1_tarski @ A @ B ) =>
% 36.77/37.03         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 36.77/37.03  thf('33', plain,
% 36.77/37.03      (![X46 : $i, X47 : $i, X48 : $i]:
% 36.77/37.03         (~ (r1_tarski @ X46 @ X47)
% 36.77/37.03          | ~ (v1_relat_1 @ X48)
% 36.77/37.03          | (r1_tarski @ (k9_relat_1 @ X48 @ X46) @ (k9_relat_1 @ X48 @ X47)))),
% 36.77/37.03      inference('cnf', [status(esa)], [t156_relat_1])).
% 36.77/37.03  thf('34', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 36.77/37.03           (k9_relat_1 @ X2 @ X0))
% 36.77/37.03          | ~ (v1_relat_1 @ X2))),
% 36.77/37.03      inference('sup-', [status(thm)], ['32', '33'])).
% 36.77/37.03  thf(t19_xboole_1, axiom,
% 36.77/37.03    (![A:$i,B:$i,C:$i]:
% 36.77/37.03     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 36.77/37.03       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 36.77/37.03  thf('35', plain,
% 36.77/37.03      (![X2 : $i, X3 : $i, X4 : $i]:
% 36.77/37.03         (~ (r1_tarski @ X2 @ X3)
% 36.77/37.03          | ~ (r1_tarski @ X2 @ X4)
% 36.77/37.03          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 36.77/37.03      inference('cnf', [status(esa)], [t19_xboole_1])).
% 36.77/37.03  thf('36', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.77/37.03         (~ (v1_relat_1 @ X1)
% 36.77/37.03          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 36.77/37.03             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 36.77/37.03          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 36.77/37.03      inference('sup-', [status(thm)], ['34', '35'])).
% 36.77/37.03  thf('37', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         (~ (v1_relat_1 @ X1)
% 36.77/37.03          | ~ (v1_funct_1 @ X1)
% 36.77/37.03          | (r1_tarski @ 
% 36.77/37.03             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 36.77/37.03             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 36.77/37.03          | ~ (v1_relat_1 @ X1))),
% 36.77/37.03      inference('sup-', [status(thm)], ['31', '36'])).
% 36.77/37.03  thf('38', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         ((r1_tarski @ 
% 36.77/37.03           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 36.77/37.03           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 36.77/37.03          | ~ (v1_funct_1 @ X1)
% 36.77/37.03          | ~ (v1_relat_1 @ X1))),
% 36.77/37.03      inference('simplify', [status(thm)], ['37'])).
% 36.77/37.03  thf('39', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.77/37.03         ((r1_tarski @ 
% 36.77/37.03           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 36.77/37.03           (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 36.77/37.03          | ~ (v1_relat_1 @ X1)
% 36.77/37.03          | ~ (v1_funct_1 @ X1))),
% 36.77/37.03      inference('sup+', [status(thm)], ['4', '38'])).
% 36.77/37.03  thf(t149_funct_1, conjecture,
% 36.77/37.03    (![A:$i,B:$i,C:$i]:
% 36.77/37.03     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 36.77/37.03       ( r1_tarski @
% 36.77/37.03         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 36.77/37.03         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 36.77/37.03  thf(zf_stmt_0, negated_conjecture,
% 36.77/37.03    (~( ![A:$i,B:$i,C:$i]:
% 36.77/37.03        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 36.77/37.03          ( r1_tarski @
% 36.77/37.03            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 36.77/37.03            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 36.77/37.03    inference('cnf.neg', [status(esa)], [t149_funct_1])).
% 36.77/37.03  thf('40', plain,
% 36.77/37.03      (~ (r1_tarski @ 
% 36.77/37.03          (k9_relat_1 @ sk_C @ 
% 36.77/37.03           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 36.77/37.03          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 36.77/37.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.77/37.03  thf('41', plain,
% 36.77/37.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 36.77/37.03      inference('sup+', [status(thm)], ['2', '3'])).
% 36.77/37.03  thf('42', plain,
% 36.77/37.03      (~ (r1_tarski @ 
% 36.77/37.03          (k9_relat_1 @ sk_C @ 
% 36.77/37.03           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 36.77/37.03          (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))),
% 36.77/37.03      inference('demod', [status(thm)], ['40', '41'])).
% 36.77/37.03  thf('43', plain, ((~ (v1_funct_1 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 36.77/37.03      inference('sup-', [status(thm)], ['39', '42'])).
% 36.77/37.03  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 36.77/37.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.77/37.03  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 36.77/37.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.77/37.03  thf('46', plain, ($false),
% 36.77/37.03      inference('demod', [status(thm)], ['43', '44', '45'])).
% 36.77/37.03  
% 36.77/37.03  % SZS output end Refutation
% 36.77/37.03  
% 36.77/37.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
