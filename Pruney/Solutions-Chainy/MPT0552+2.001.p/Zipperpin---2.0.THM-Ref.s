%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4dfUiqBFer

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:24 EST 2020

% Result     : Theorem 55.61s
% Output     : Refutation 55.61s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 132 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  921 (1268 expanded)
%              Number of equality atoms :   48 (  73 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k9_relat_1 @ X37 @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X34 @ X35 ) @ X36 )
        = ( k8_relat_1 @ X34 @ ( k7_relat_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X28 @ X27 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k9_relat_1 @ X37 @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) @ X0 )
        = ( k9_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) @ X0 )
        = ( k9_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k9_relat_1 @ X37 @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) @ X23 )
        = ( k7_relat_1 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('20',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k9_relat_1 @ X37 @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X34 @ X35 ) @ X36 )
        = ( k8_relat_1 @ X34 @ ( k7_relat_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('27',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k9_relat_1 @ X37 @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( ( k8_relat_1 @ X30 @ X29 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X1 ) @ X0 )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X1 ) @ X0 )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k9_relat_1 @ X37 @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('44',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k9_relat_1 @ X37 @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('45',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X41 @ X42 ) @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( r1_tarski @ ( k2_relat_1 @ X40 ) @ ( k2_relat_1 @ X39 ) )
      | ~ ( r1_tarski @ X40 @ X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['42','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X1 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','57'])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X1 ) @ X2 ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X2 @ X1 ) @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X2 @ X1 ) @ X2 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('65',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4dfUiqBFer
% 0.15/0.37  % Computer   : n010.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:48:29 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 55.61/55.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 55.61/55.83  % Solved by: fo/fo7.sh
% 55.61/55.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 55.61/55.83  % done 11298 iterations in 55.334s
% 55.61/55.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 55.61/55.83  % SZS output start Refutation
% 55.61/55.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 55.61/55.83  thf(sk_C_type, type, sk_C: $i).
% 55.61/55.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 55.61/55.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 55.61/55.83  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 55.61/55.83  thf(sk_B_type, type, sk_B: $i).
% 55.61/55.83  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 55.61/55.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 55.61/55.83  thf(sk_A_type, type, sk_A: $i).
% 55.61/55.83  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 55.61/55.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 55.61/55.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 55.61/55.83  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 55.61/55.83  thf(t148_relat_1, axiom,
% 55.61/55.83    (![A:$i,B:$i]:
% 55.61/55.83     ( ( v1_relat_1 @ B ) =>
% 55.61/55.83       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 55.61/55.83  thf('0', plain,
% 55.61/55.83      (![X37 : $i, X38 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k7_relat_1 @ X37 @ X38)) = (k9_relat_1 @ X37 @ X38))
% 55.61/55.83          | ~ (v1_relat_1 @ X37))),
% 55.61/55.83      inference('cnf', [status(esa)], [t148_relat_1])).
% 55.61/55.83  thf(t140_relat_1, axiom,
% 55.61/55.83    (![A:$i,B:$i,C:$i]:
% 55.61/55.83     ( ( v1_relat_1 @ C ) =>
% 55.61/55.83       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 55.61/55.83         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 55.61/55.83  thf('1', plain,
% 55.61/55.83      (![X34 : $i, X35 : $i, X36 : $i]:
% 55.61/55.83         (((k7_relat_1 @ (k8_relat_1 @ X34 @ X35) @ X36)
% 55.61/55.83            = (k8_relat_1 @ X34 @ (k7_relat_1 @ X35 @ X36)))
% 55.61/55.83          | ~ (v1_relat_1 @ X35))),
% 55.61/55.83      inference('cnf', [status(esa)], [t140_relat_1])).
% 55.61/55.83  thf(t119_relat_1, axiom,
% 55.61/55.83    (![A:$i,B:$i]:
% 55.61/55.83     ( ( v1_relat_1 @ B ) =>
% 55.61/55.83       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 55.61/55.83         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 55.61/55.83  thf('2', plain,
% 55.61/55.83      (![X27 : $i, X28 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k8_relat_1 @ X28 @ X27))
% 55.61/55.83            = (k3_xboole_0 @ (k2_relat_1 @ X27) @ X28))
% 55.61/55.83          | ~ (v1_relat_1 @ X27))),
% 55.61/55.83      inference('cnf', [status(esa)], [t119_relat_1])).
% 55.61/55.83  thf('3', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 55.61/55.83            = (k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))
% 55.61/55.83          | ~ (v1_relat_1 @ X1)
% 55.61/55.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 55.61/55.83      inference('sup+', [status(thm)], ['1', '2'])).
% 55.61/55.83  thf(dt_k7_relat_1, axiom,
% 55.61/55.83    (![A:$i,B:$i]:
% 55.61/55.83     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 55.61/55.83  thf('4', plain,
% 55.61/55.83      (![X17 : $i, X18 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 55.61/55.83      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 55.61/55.83  thf('5', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X1)
% 55.61/55.83          | ((k2_relat_1 @ (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 55.61/55.83              = (k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)))),
% 55.61/55.83      inference('clc', [status(thm)], ['3', '4'])).
% 55.61/55.83  thf('6', plain,
% 55.61/55.83      (![X37 : $i, X38 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k7_relat_1 @ X37 @ X38)) = (k9_relat_1 @ X37 @ X38))
% 55.61/55.83          | ~ (v1_relat_1 @ X37))),
% 55.61/55.83      inference('cnf', [status(esa)], [t148_relat_1])).
% 55.61/55.83  thf('7', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (((k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)) @ X0)
% 55.61/55.83            = (k9_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1))
% 55.61/55.83          | ~ (v1_relat_1 @ X2)
% 55.61/55.83          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X2)))),
% 55.61/55.83      inference('sup+', [status(thm)], ['5', '6'])).
% 55.61/55.83  thf(dt_k8_relat_1, axiom,
% 55.61/55.83    (![A:$i,B:$i]:
% 55.61/55.83     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 55.61/55.83  thf('8', plain,
% 55.61/55.83      (![X19 : $i, X20 : $i]:
% 55.61/55.83         ((v1_relat_1 @ (k8_relat_1 @ X19 @ X20)) | ~ (v1_relat_1 @ X20))),
% 55.61/55.83      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 55.61/55.83  thf('9', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X2)
% 55.61/55.83          | ((k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)) @ X0)
% 55.61/55.83              = (k9_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1)))),
% 55.61/55.83      inference('clc', [status(thm)], ['7', '8'])).
% 55.61/55.83  thf(commutativity_k2_tarski, axiom,
% 55.61/55.83    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 55.61/55.83  thf('10', plain,
% 55.61/55.83      (![X3 : $i, X4 : $i]: ((k2_tarski @ X4 @ X3) = (k2_tarski @ X3 @ X4))),
% 55.61/55.83      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 55.61/55.83  thf(t12_setfam_1, axiom,
% 55.61/55.83    (![A:$i,B:$i]:
% 55.61/55.83     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 55.61/55.83  thf('11', plain,
% 55.61/55.83      (![X10 : $i, X11 : $i]:
% 55.61/55.83         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 55.61/55.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 55.61/55.83  thf('12', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]:
% 55.61/55.83         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 55.61/55.83      inference('sup+', [status(thm)], ['10', '11'])).
% 55.61/55.83  thf('13', plain,
% 55.61/55.83      (![X10 : $i, X11 : $i]:
% 55.61/55.83         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 55.61/55.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 55.61/55.83  thf('14', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 55.61/55.83      inference('sup+', [status(thm)], ['12', '13'])).
% 55.61/55.83  thf('15', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 55.61/55.83            = (k3_xboole_0 @ X2 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 55.61/55.83          | ~ (v1_relat_1 @ X1))),
% 55.61/55.83      inference('sup+', [status(thm)], ['9', '14'])).
% 55.61/55.83  thf('16', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 55.61/55.83            = (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 55.61/55.83          | ~ (v1_relat_1 @ X1)
% 55.61/55.83          | ~ (v1_relat_1 @ X1))),
% 55.61/55.83      inference('sup+', [status(thm)], ['0', '15'])).
% 55.61/55.83  thf('17', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X1)
% 55.61/55.83          | ((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 55.61/55.83              = (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0))))),
% 55.61/55.83      inference('simplify', [status(thm)], ['16'])).
% 55.61/55.83  thf('18', plain,
% 55.61/55.83      (![X37 : $i, X38 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k7_relat_1 @ X37 @ X38)) = (k9_relat_1 @ X37 @ X38))
% 55.61/55.83          | ~ (v1_relat_1 @ X37))),
% 55.61/55.83      inference('cnf', [status(esa)], [t148_relat_1])).
% 55.61/55.83  thf(t100_relat_1, axiom,
% 55.61/55.83    (![A:$i,B:$i,C:$i]:
% 55.61/55.83     ( ( v1_relat_1 @ C ) =>
% 55.61/55.83       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 55.61/55.83         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 55.61/55.83  thf('19', plain,
% 55.61/55.83      (![X21 : $i, X22 : $i, X23 : $i]:
% 55.61/55.83         (((k7_relat_1 @ (k7_relat_1 @ X21 @ X22) @ X23)
% 55.61/55.83            = (k7_relat_1 @ X21 @ (k3_xboole_0 @ X22 @ X23)))
% 55.61/55.83          | ~ (v1_relat_1 @ X21))),
% 55.61/55.83      inference('cnf', [status(esa)], [t100_relat_1])).
% 55.61/55.83  thf('20', plain,
% 55.61/55.83      (![X37 : $i, X38 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k7_relat_1 @ X37 @ X38)) = (k9_relat_1 @ X37 @ X38))
% 55.61/55.83          | ~ (v1_relat_1 @ X37))),
% 55.61/55.83      inference('cnf', [status(esa)], [t148_relat_1])).
% 55.61/55.83  thf('21', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 55.61/55.83            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 55.61/55.83          | ~ (v1_relat_1 @ X2)
% 55.61/55.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 55.61/55.83      inference('sup+', [status(thm)], ['19', '20'])).
% 55.61/55.83  thf('22', plain,
% 55.61/55.83      (![X17 : $i, X18 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 55.61/55.83      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 55.61/55.83  thf('23', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X2)
% 55.61/55.83          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 55.61/55.83              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 55.61/55.83      inference('clc', [status(thm)], ['21', '22'])).
% 55.61/55.83  thf('24', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 55.61/55.83            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 55.61/55.83          | ~ (v1_relat_1 @ X2)
% 55.61/55.83          | ~ (v1_relat_1 @ X2))),
% 55.61/55.83      inference('sup+', [status(thm)], ['18', '23'])).
% 55.61/55.83  thf('25', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X2)
% 55.61/55.83          | ((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 55.61/55.83              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 55.61/55.83      inference('simplify', [status(thm)], ['24'])).
% 55.61/55.83  thf('26', plain,
% 55.61/55.83      (![X34 : $i, X35 : $i, X36 : $i]:
% 55.61/55.83         (((k7_relat_1 @ (k8_relat_1 @ X34 @ X35) @ X36)
% 55.61/55.83            = (k8_relat_1 @ X34 @ (k7_relat_1 @ X35 @ X36)))
% 55.61/55.83          | ~ (v1_relat_1 @ X35))),
% 55.61/55.83      inference('cnf', [status(esa)], [t140_relat_1])).
% 55.61/55.83  thf('27', plain,
% 55.61/55.83      (![X37 : $i, X38 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k7_relat_1 @ X37 @ X38)) = (k9_relat_1 @ X37 @ X38))
% 55.61/55.83          | ~ (v1_relat_1 @ X37))),
% 55.61/55.83      inference('cnf', [status(esa)], [t148_relat_1])).
% 55.61/55.83  thf(d10_xboole_0, axiom,
% 55.61/55.83    (![A:$i,B:$i]:
% 55.61/55.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 55.61/55.83  thf('28', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 55.61/55.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 55.61/55.83  thf('29', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 55.61/55.83      inference('simplify', [status(thm)], ['28'])).
% 55.61/55.83  thf(t125_relat_1, axiom,
% 55.61/55.83    (![A:$i,B:$i]:
% 55.61/55.83     ( ( v1_relat_1 @ B ) =>
% 55.61/55.83       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 55.61/55.83         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 55.61/55.83  thf('30', plain,
% 55.61/55.83      (![X29 : $i, X30 : $i]:
% 55.61/55.83         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 55.61/55.83          | ((k8_relat_1 @ X30 @ X29) = (X29))
% 55.61/55.83          | ~ (v1_relat_1 @ X29))),
% 55.61/55.83      inference('cnf', [status(esa)], [t125_relat_1])).
% 55.61/55.83  thf('31', plain,
% 55.61/55.83      (![X0 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 55.61/55.83      inference('sup-', [status(thm)], ['29', '30'])).
% 55.61/55.83  thf('32', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]:
% 55.61/55.83         (((k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ (k7_relat_1 @ X1 @ X0))
% 55.61/55.83            = (k7_relat_1 @ X1 @ X0))
% 55.61/55.83          | ~ (v1_relat_1 @ X1)
% 55.61/55.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 55.61/55.83      inference('sup+', [status(thm)], ['27', '31'])).
% 55.61/55.83  thf('33', plain,
% 55.61/55.83      (![X17 : $i, X18 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 55.61/55.83      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 55.61/55.83  thf('34', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X1)
% 55.61/55.83          | ((k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ (k7_relat_1 @ X1 @ X0))
% 55.61/55.83              = (k7_relat_1 @ X1 @ X0)))),
% 55.61/55.83      inference('clc', [status(thm)], ['32', '33'])).
% 55.61/55.83  thf('35', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]:
% 55.61/55.83         (((k7_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ X1) @ X0)
% 55.61/55.83            = (k7_relat_1 @ X1 @ X0))
% 55.61/55.83          | ~ (v1_relat_1 @ X1)
% 55.61/55.83          | ~ (v1_relat_1 @ X1))),
% 55.61/55.83      inference('sup+', [status(thm)], ['26', '34'])).
% 55.61/55.83  thf('36', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X1)
% 55.61/55.83          | ((k7_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ X1) @ X0)
% 55.61/55.83              = (k7_relat_1 @ X1 @ X0)))),
% 55.61/55.83      inference('simplify', [status(thm)], ['35'])).
% 55.61/55.83  thf('37', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X2)
% 55.61/55.83          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 55.61/55.83              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 55.61/55.83      inference('clc', [status(thm)], ['21', '22'])).
% 55.61/55.83  thf('38', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 55.61/55.83      inference('sup+', [status(thm)], ['12', '13'])).
% 55.61/55.83  thf('39', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X2)
% 55.61/55.83          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 55.61/55.83              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 55.61/55.83      inference('clc', [status(thm)], ['21', '22'])).
% 55.61/55.83  thf('40', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 55.61/55.83            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 55.61/55.83          | ~ (v1_relat_1 @ X2))),
% 55.61/55.83      inference('sup+', [status(thm)], ['38', '39'])).
% 55.61/55.83  thf('41', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (((k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 55.61/55.83            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 55.61/55.83          | ~ (v1_relat_1 @ X2)
% 55.61/55.83          | ~ (v1_relat_1 @ X2))),
% 55.61/55.83      inference('sup+', [status(thm)], ['37', '40'])).
% 55.61/55.83  thf('42', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X2)
% 55.61/55.83          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 55.61/55.83              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)))),
% 55.61/55.83      inference('simplify', [status(thm)], ['41'])).
% 55.61/55.83  thf('43', plain,
% 55.61/55.83      (![X37 : $i, X38 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k7_relat_1 @ X37 @ X38)) = (k9_relat_1 @ X37 @ X38))
% 55.61/55.83          | ~ (v1_relat_1 @ X37))),
% 55.61/55.83      inference('cnf', [status(esa)], [t148_relat_1])).
% 55.61/55.83  thf('44', plain,
% 55.61/55.83      (![X37 : $i, X38 : $i]:
% 55.61/55.83         (((k2_relat_1 @ (k7_relat_1 @ X37 @ X38)) = (k9_relat_1 @ X37 @ X38))
% 55.61/55.83          | ~ (v1_relat_1 @ X37))),
% 55.61/55.83      inference('cnf', [status(esa)], [t148_relat_1])).
% 55.61/55.83  thf(t88_relat_1, axiom,
% 55.61/55.83    (![A:$i,B:$i]:
% 55.61/55.83     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 55.61/55.83  thf('45', plain,
% 55.61/55.83      (![X41 : $i, X42 : $i]:
% 55.61/55.83         ((r1_tarski @ (k7_relat_1 @ X41 @ X42) @ X41) | ~ (v1_relat_1 @ X41))),
% 55.61/55.83      inference('cnf', [status(esa)], [t88_relat_1])).
% 55.61/55.83  thf(t25_relat_1, axiom,
% 55.61/55.83    (![A:$i]:
% 55.61/55.83     ( ( v1_relat_1 @ A ) =>
% 55.61/55.83       ( ![B:$i]:
% 55.61/55.83         ( ( v1_relat_1 @ B ) =>
% 55.61/55.83           ( ( r1_tarski @ A @ B ) =>
% 55.61/55.83             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 55.61/55.83               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 55.61/55.83  thf('46', plain,
% 55.61/55.83      (![X39 : $i, X40 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X39)
% 55.61/55.83          | (r1_tarski @ (k2_relat_1 @ X40) @ (k2_relat_1 @ X39))
% 55.61/55.83          | ~ (r1_tarski @ X40 @ X39)
% 55.61/55.83          | ~ (v1_relat_1 @ X40))),
% 55.61/55.83      inference('cnf', [status(esa)], [t25_relat_1])).
% 55.61/55.83  thf('47', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X0)
% 55.61/55.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 55.61/55.83          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 55.61/55.83             (k2_relat_1 @ X0))
% 55.61/55.83          | ~ (v1_relat_1 @ X0))),
% 55.61/55.83      inference('sup-', [status(thm)], ['45', '46'])).
% 55.61/55.83  thf('48', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]:
% 55.61/55.83         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 55.61/55.83           (k2_relat_1 @ X0))
% 55.61/55.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 55.61/55.83          | ~ (v1_relat_1 @ X0))),
% 55.61/55.83      inference('simplify', [status(thm)], ['47'])).
% 55.61/55.83  thf('49', plain,
% 55.61/55.83      (![X17 : $i, X18 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 55.61/55.83      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 55.61/55.83  thf('50', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X0)
% 55.61/55.83          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 55.61/55.83             (k2_relat_1 @ X0)))),
% 55.61/55.83      inference('clc', [status(thm)], ['48', '49'])).
% 55.61/55.83  thf('51', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]:
% 55.61/55.83         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 55.61/55.83          | ~ (v1_relat_1 @ X1)
% 55.61/55.83          | ~ (v1_relat_1 @ X1))),
% 55.61/55.83      inference('sup+', [status(thm)], ['44', '50'])).
% 55.61/55.83  thf('52', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X1)
% 55.61/55.83          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 55.61/55.83      inference('simplify', [status(thm)], ['51'])).
% 55.61/55.83  thf('53', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 55.61/55.83           (k9_relat_1 @ X1 @ X0))
% 55.61/55.83          | ~ (v1_relat_1 @ X1)
% 55.61/55.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 55.61/55.83      inference('sup+', [status(thm)], ['43', '52'])).
% 55.61/55.83  thf('54', plain,
% 55.61/55.83      (![X17 : $i, X18 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 55.61/55.83      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 55.61/55.83  thf('55', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X1)
% 55.61/55.83          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 55.61/55.83             (k9_relat_1 @ X1 @ X0)))),
% 55.61/55.83      inference('clc', [status(thm)], ['53', '54'])).
% 55.61/55.83  thf('56', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 55.61/55.83           (k9_relat_1 @ X2 @ X0))
% 55.61/55.83          | ~ (v1_relat_1 @ X2)
% 55.61/55.83          | ~ (v1_relat_1 @ X2))),
% 55.61/55.83      inference('sup+', [status(thm)], ['42', '55'])).
% 55.61/55.83  thf('57', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X2)
% 55.61/55.83          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 55.61/55.83             (k9_relat_1 @ X2 @ X0)))),
% 55.61/55.83      inference('simplify', [status(thm)], ['56'])).
% 55.61/55.83  thf('58', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 55.61/55.83           (k9_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ X1) @ X2))
% 55.61/55.83          | ~ (v1_relat_1 @ X1)
% 55.61/55.83          | ~ (v1_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ X1)))),
% 55.61/55.83      inference('sup+', [status(thm)], ['36', '57'])).
% 55.61/55.83  thf('59', plain,
% 55.61/55.83      (![X19 : $i, X20 : $i]:
% 55.61/55.83         ((v1_relat_1 @ (k8_relat_1 @ X19 @ X20)) | ~ (v1_relat_1 @ X20))),
% 55.61/55.83      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 55.61/55.83  thf('60', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X1)
% 55.61/55.83          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 55.61/55.83             (k9_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ X1) @ X2)))),
% 55.61/55.83      inference('clc', [status(thm)], ['58', '59'])).
% 55.61/55.83  thf('61', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 55.61/55.83           (k9_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X2 @ X1) @ X2) @ X0))
% 55.61/55.83          | ~ (v1_relat_1 @ X2)
% 55.61/55.83          | ~ (v1_relat_1 @ X2))),
% 55.61/55.83      inference('sup+', [status(thm)], ['25', '60'])).
% 55.61/55.83  thf('62', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X2)
% 55.61/55.83          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 55.61/55.83             (k9_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X2 @ X1) @ X2) @ X0)))),
% 55.61/55.83      inference('simplify', [status(thm)], ['61'])).
% 55.61/55.83  thf('63', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 55.61/55.83           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 55.61/55.83          | ~ (v1_relat_1 @ X1)
% 55.61/55.83          | ~ (v1_relat_1 @ X1))),
% 55.61/55.83      inference('sup+', [status(thm)], ['17', '62'])).
% 55.61/55.83  thf('64', plain,
% 55.61/55.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.61/55.83         (~ (v1_relat_1 @ X1)
% 55.61/55.83          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 55.61/55.83             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))))),
% 55.61/55.83      inference('simplify', [status(thm)], ['63'])).
% 55.61/55.83  thf(t154_relat_1, conjecture,
% 55.61/55.83    (![A:$i,B:$i,C:$i]:
% 55.61/55.83     ( ( v1_relat_1 @ C ) =>
% 55.61/55.83       ( r1_tarski @
% 55.61/55.83         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 55.61/55.83         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 55.61/55.83  thf(zf_stmt_0, negated_conjecture,
% 55.61/55.83    (~( ![A:$i,B:$i,C:$i]:
% 55.61/55.83        ( ( v1_relat_1 @ C ) =>
% 55.61/55.83          ( r1_tarski @
% 55.61/55.83            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 55.61/55.83            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 55.61/55.83    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 55.61/55.83  thf('65', plain,
% 55.61/55.83      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 55.61/55.83          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 55.61/55.83           (k9_relat_1 @ sk_C @ sk_B)))),
% 55.61/55.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.61/55.83  thf('66', plain, (~ (v1_relat_1 @ sk_C)),
% 55.61/55.83      inference('sup-', [status(thm)], ['64', '65'])).
% 55.61/55.83  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 55.61/55.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.61/55.83  thf('68', plain, ($false), inference('demod', [status(thm)], ['66', '67'])).
% 55.61/55.83  
% 55.61/55.83  % SZS output end Refutation
% 55.61/55.83  
% 55.61/55.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
