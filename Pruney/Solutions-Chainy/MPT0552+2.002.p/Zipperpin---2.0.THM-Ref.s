%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7NNRmYgmXQ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:24 EST 2020

% Result     : Theorem 46.92s
% Output     : Refutation 46.92s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 132 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  900 (1268 expanded)
%              Number of equality atoms :   46 (  73 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X35 @ X36 ) @ X37 )
        = ( k8_relat_1 @ X35 @ ( k7_relat_1 @ X36 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
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

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) @ X23 )
        = ( k7_relat_1 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('19',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X35 @ X36 ) @ X37 )
        = ( k8_relat_1 @ X35 @ ( k7_relat_1 @ X36 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('27',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
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
    inference(clc,[status(thm)],['20','21'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('42',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('43',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X42 @ X43 ) @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( r1_tarski @ ( k2_relat_1 @ X41 ) @ ( k2_relat_1 @ X40 ) )
      | ~ ( r1_tarski @ X41 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X1 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','55'])).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X1 ) @ X2 ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X2 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X2 @ X0 ) @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('63',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7NNRmYgmXQ
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 46.92/47.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 46.92/47.17  % Solved by: fo/fo7.sh
% 46.92/47.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 46.92/47.17  % done 9975 iterations in 46.704s
% 46.92/47.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 46.92/47.17  % SZS output start Refutation
% 46.92/47.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 46.92/47.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 46.92/47.17  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 46.92/47.17  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 46.92/47.17  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 46.92/47.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 46.92/47.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 46.92/47.17  thf(sk_B_type, type, sk_B: $i).
% 46.92/47.17  thf(sk_C_type, type, sk_C: $i).
% 46.92/47.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 46.92/47.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 46.92/47.17  thf(sk_A_type, type, sk_A: $i).
% 46.92/47.17  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 46.92/47.17  thf(t148_relat_1, axiom,
% 46.92/47.17    (![A:$i,B:$i]:
% 46.92/47.17     ( ( v1_relat_1 @ B ) =>
% 46.92/47.17       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 46.92/47.17  thf('0', plain,
% 46.92/47.17      (![X38 : $i, X39 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 46.92/47.17          | ~ (v1_relat_1 @ X38))),
% 46.92/47.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.92/47.17  thf(t140_relat_1, axiom,
% 46.92/47.17    (![A:$i,B:$i,C:$i]:
% 46.92/47.17     ( ( v1_relat_1 @ C ) =>
% 46.92/47.17       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 46.92/47.17         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 46.92/47.17  thf('1', plain,
% 46.92/47.17      (![X35 : $i, X36 : $i, X37 : $i]:
% 46.92/47.17         (((k7_relat_1 @ (k8_relat_1 @ X35 @ X36) @ X37)
% 46.92/47.17            = (k8_relat_1 @ X35 @ (k7_relat_1 @ X36 @ X37)))
% 46.92/47.17          | ~ (v1_relat_1 @ X36))),
% 46.92/47.17      inference('cnf', [status(esa)], [t140_relat_1])).
% 46.92/47.17  thf(t119_relat_1, axiom,
% 46.92/47.17    (![A:$i,B:$i]:
% 46.92/47.17     ( ( v1_relat_1 @ B ) =>
% 46.92/47.17       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 46.92/47.17         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 46.92/47.17  thf('2', plain,
% 46.92/47.17      (![X27 : $i, X28 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k8_relat_1 @ X28 @ X27))
% 46.92/47.17            = (k3_xboole_0 @ (k2_relat_1 @ X27) @ X28))
% 46.92/47.17          | ~ (v1_relat_1 @ X27))),
% 46.92/47.17      inference('cnf', [status(esa)], [t119_relat_1])).
% 46.92/47.17  thf('3', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 46.92/47.17            = (k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))
% 46.92/47.17          | ~ (v1_relat_1 @ X1)
% 46.92/47.17          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 46.92/47.17      inference('sup+', [status(thm)], ['1', '2'])).
% 46.92/47.17  thf(dt_k7_relat_1, axiom,
% 46.92/47.17    (![A:$i,B:$i]:
% 46.92/47.17     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 46.92/47.17  thf('4', plain,
% 46.92/47.17      (![X17 : $i, X18 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 46.92/47.17      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 46.92/47.17  thf('5', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X1)
% 46.92/47.17          | ((k2_relat_1 @ (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 46.92/47.17              = (k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)))),
% 46.92/47.17      inference('clc', [status(thm)], ['3', '4'])).
% 46.92/47.17  thf('6', plain,
% 46.92/47.17      (![X38 : $i, X39 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 46.92/47.17          | ~ (v1_relat_1 @ X38))),
% 46.92/47.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.92/47.17  thf('7', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (((k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)) @ X0)
% 46.92/47.17            = (k9_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1))
% 46.92/47.17          | ~ (v1_relat_1 @ X2)
% 46.92/47.17          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X2)))),
% 46.92/47.17      inference('sup+', [status(thm)], ['5', '6'])).
% 46.92/47.17  thf(dt_k8_relat_1, axiom,
% 46.92/47.17    (![A:$i,B:$i]:
% 46.92/47.17     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 46.92/47.17  thf('8', plain,
% 46.92/47.17      (![X19 : $i, X20 : $i]:
% 46.92/47.17         ((v1_relat_1 @ (k8_relat_1 @ X19 @ X20)) | ~ (v1_relat_1 @ X20))),
% 46.92/47.17      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 46.92/47.17  thf('9', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X2)
% 46.92/47.17          | ((k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)) @ X0)
% 46.92/47.17              = (k9_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1)))),
% 46.92/47.17      inference('clc', [status(thm)], ['7', '8'])).
% 46.92/47.17  thf('10', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (((k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2)
% 46.92/47.17            = (k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 46.92/47.17          | ~ (v1_relat_1 @ X1)
% 46.92/47.17          | ~ (v1_relat_1 @ X1))),
% 46.92/47.17      inference('sup+', [status(thm)], ['0', '9'])).
% 46.92/47.17  thf('11', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X1)
% 46.92/47.17          | ((k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2)
% 46.92/47.17              = (k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)))),
% 46.92/47.17      inference('simplify', [status(thm)], ['10'])).
% 46.92/47.17  thf('12', plain,
% 46.92/47.17      (![X38 : $i, X39 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 46.92/47.17          | ~ (v1_relat_1 @ X38))),
% 46.92/47.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.92/47.17  thf(commutativity_k2_tarski, axiom,
% 46.92/47.17    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 46.92/47.17  thf('13', plain,
% 46.92/47.17      (![X3 : $i, X4 : $i]: ((k2_tarski @ X4 @ X3) = (k2_tarski @ X3 @ X4))),
% 46.92/47.17      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 46.92/47.17  thf(t12_setfam_1, axiom,
% 46.92/47.17    (![A:$i,B:$i]:
% 46.92/47.17     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 46.92/47.17  thf('14', plain,
% 46.92/47.17      (![X10 : $i, X11 : $i]:
% 46.92/47.17         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 46.92/47.17      inference('cnf', [status(esa)], [t12_setfam_1])).
% 46.92/47.17  thf('15', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]:
% 46.92/47.17         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 46.92/47.17      inference('sup+', [status(thm)], ['13', '14'])).
% 46.92/47.17  thf('16', plain,
% 46.92/47.17      (![X10 : $i, X11 : $i]:
% 46.92/47.17         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 46.92/47.17      inference('cnf', [status(esa)], [t12_setfam_1])).
% 46.92/47.17  thf('17', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 46.92/47.17      inference('sup+', [status(thm)], ['15', '16'])).
% 46.92/47.17  thf(t100_relat_1, axiom,
% 46.92/47.17    (![A:$i,B:$i,C:$i]:
% 46.92/47.17     ( ( v1_relat_1 @ C ) =>
% 46.92/47.17       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 46.92/47.17         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 46.92/47.17  thf('18', plain,
% 46.92/47.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 46.92/47.17         (((k7_relat_1 @ (k7_relat_1 @ X21 @ X22) @ X23)
% 46.92/47.17            = (k7_relat_1 @ X21 @ (k3_xboole_0 @ X22 @ X23)))
% 46.92/47.17          | ~ (v1_relat_1 @ X21))),
% 46.92/47.17      inference('cnf', [status(esa)], [t100_relat_1])).
% 46.92/47.17  thf('19', plain,
% 46.92/47.17      (![X38 : $i, X39 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 46.92/47.17          | ~ (v1_relat_1 @ X38))),
% 46.92/47.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.92/47.17  thf('20', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 46.92/47.17            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 46.92/47.17          | ~ (v1_relat_1 @ X2)
% 46.92/47.17          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 46.92/47.17      inference('sup+', [status(thm)], ['18', '19'])).
% 46.92/47.17  thf('21', plain,
% 46.92/47.17      (![X17 : $i, X18 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 46.92/47.17      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 46.92/47.17  thf('22', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X2)
% 46.92/47.17          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 46.92/47.17              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 46.92/47.17      inference('clc', [status(thm)], ['20', '21'])).
% 46.92/47.17  thf('23', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 46.92/47.17            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 46.92/47.17          | ~ (v1_relat_1 @ X2))),
% 46.92/47.17      inference('sup+', [status(thm)], ['17', '22'])).
% 46.92/47.17  thf('24', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 46.92/47.17            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 46.92/47.17          | ~ (v1_relat_1 @ X2)
% 46.92/47.17          | ~ (v1_relat_1 @ X2))),
% 46.92/47.17      inference('sup+', [status(thm)], ['12', '23'])).
% 46.92/47.17  thf('25', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X2)
% 46.92/47.17          | ((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 46.92/47.17              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)))),
% 46.92/47.17      inference('simplify', [status(thm)], ['24'])).
% 46.92/47.17  thf('26', plain,
% 46.92/47.17      (![X35 : $i, X36 : $i, X37 : $i]:
% 46.92/47.17         (((k7_relat_1 @ (k8_relat_1 @ X35 @ X36) @ X37)
% 46.92/47.17            = (k8_relat_1 @ X35 @ (k7_relat_1 @ X36 @ X37)))
% 46.92/47.17          | ~ (v1_relat_1 @ X36))),
% 46.92/47.17      inference('cnf', [status(esa)], [t140_relat_1])).
% 46.92/47.17  thf('27', plain,
% 46.92/47.17      (![X38 : $i, X39 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 46.92/47.17          | ~ (v1_relat_1 @ X38))),
% 46.92/47.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.92/47.17  thf(d10_xboole_0, axiom,
% 46.92/47.17    (![A:$i,B:$i]:
% 46.92/47.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 46.92/47.17  thf('28', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 46.92/47.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 46.92/47.17  thf('29', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 46.92/47.17      inference('simplify', [status(thm)], ['28'])).
% 46.92/47.17  thf(t125_relat_1, axiom,
% 46.92/47.17    (![A:$i,B:$i]:
% 46.92/47.17     ( ( v1_relat_1 @ B ) =>
% 46.92/47.17       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 46.92/47.17         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 46.92/47.17  thf('30', plain,
% 46.92/47.17      (![X29 : $i, X30 : $i]:
% 46.92/47.17         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 46.92/47.17          | ((k8_relat_1 @ X30 @ X29) = (X29))
% 46.92/47.17          | ~ (v1_relat_1 @ X29))),
% 46.92/47.17      inference('cnf', [status(esa)], [t125_relat_1])).
% 46.92/47.17  thf('31', plain,
% 46.92/47.17      (![X0 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 46.92/47.17      inference('sup-', [status(thm)], ['29', '30'])).
% 46.92/47.17  thf('32', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]:
% 46.92/47.17         (((k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ (k7_relat_1 @ X1 @ X0))
% 46.92/47.17            = (k7_relat_1 @ X1 @ X0))
% 46.92/47.17          | ~ (v1_relat_1 @ X1)
% 46.92/47.17          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 46.92/47.17      inference('sup+', [status(thm)], ['27', '31'])).
% 46.92/47.17  thf('33', plain,
% 46.92/47.17      (![X17 : $i, X18 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 46.92/47.17      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 46.92/47.17  thf('34', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X1)
% 46.92/47.17          | ((k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ (k7_relat_1 @ X1 @ X0))
% 46.92/47.17              = (k7_relat_1 @ X1 @ X0)))),
% 46.92/47.17      inference('clc', [status(thm)], ['32', '33'])).
% 46.92/47.17  thf('35', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]:
% 46.92/47.17         (((k7_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ X1) @ X0)
% 46.92/47.17            = (k7_relat_1 @ X1 @ X0))
% 46.92/47.17          | ~ (v1_relat_1 @ X1)
% 46.92/47.17          | ~ (v1_relat_1 @ X1))),
% 46.92/47.17      inference('sup+', [status(thm)], ['26', '34'])).
% 46.92/47.17  thf('36', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X1)
% 46.92/47.17          | ((k7_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ X1) @ X0)
% 46.92/47.17              = (k7_relat_1 @ X1 @ X0)))),
% 46.92/47.17      inference('simplify', [status(thm)], ['35'])).
% 46.92/47.17  thf('37', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X2)
% 46.92/47.17          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 46.92/47.17              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 46.92/47.17      inference('clc', [status(thm)], ['20', '21'])).
% 46.92/47.17  thf('38', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 46.92/47.17            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 46.92/47.17          | ~ (v1_relat_1 @ X2))),
% 46.92/47.17      inference('sup+', [status(thm)], ['17', '22'])).
% 46.92/47.17  thf('39', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (((k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 46.92/47.17            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 46.92/47.17          | ~ (v1_relat_1 @ X2)
% 46.92/47.17          | ~ (v1_relat_1 @ X2))),
% 46.92/47.17      inference('sup+', [status(thm)], ['37', '38'])).
% 46.92/47.17  thf('40', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X2)
% 46.92/47.17          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 46.92/47.17              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)))),
% 46.92/47.17      inference('simplify', [status(thm)], ['39'])).
% 46.92/47.17  thf('41', plain,
% 46.92/47.17      (![X38 : $i, X39 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 46.92/47.17          | ~ (v1_relat_1 @ X38))),
% 46.92/47.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.92/47.17  thf('42', plain,
% 46.92/47.17      (![X38 : $i, X39 : $i]:
% 46.92/47.17         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 46.92/47.17          | ~ (v1_relat_1 @ X38))),
% 46.92/47.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.92/47.17  thf(t88_relat_1, axiom,
% 46.92/47.17    (![A:$i,B:$i]:
% 46.92/47.17     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 46.92/47.17  thf('43', plain,
% 46.92/47.17      (![X42 : $i, X43 : $i]:
% 46.92/47.17         ((r1_tarski @ (k7_relat_1 @ X42 @ X43) @ X42) | ~ (v1_relat_1 @ X42))),
% 46.92/47.17      inference('cnf', [status(esa)], [t88_relat_1])).
% 46.92/47.17  thf(t25_relat_1, axiom,
% 46.92/47.17    (![A:$i]:
% 46.92/47.17     ( ( v1_relat_1 @ A ) =>
% 46.92/47.17       ( ![B:$i]:
% 46.92/47.17         ( ( v1_relat_1 @ B ) =>
% 46.92/47.17           ( ( r1_tarski @ A @ B ) =>
% 46.92/47.17             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 46.92/47.17               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 46.92/47.17  thf('44', plain,
% 46.92/47.17      (![X40 : $i, X41 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X40)
% 46.92/47.17          | (r1_tarski @ (k2_relat_1 @ X41) @ (k2_relat_1 @ X40))
% 46.92/47.17          | ~ (r1_tarski @ X41 @ X40)
% 46.92/47.17          | ~ (v1_relat_1 @ X41))),
% 46.92/47.17      inference('cnf', [status(esa)], [t25_relat_1])).
% 46.92/47.17  thf('45', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X0)
% 46.92/47.17          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 46.92/47.17          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 46.92/47.17             (k2_relat_1 @ X0))
% 46.92/47.17          | ~ (v1_relat_1 @ X0))),
% 46.92/47.17      inference('sup-', [status(thm)], ['43', '44'])).
% 46.92/47.17  thf('46', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]:
% 46.92/47.17         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 46.92/47.17           (k2_relat_1 @ X0))
% 46.92/47.17          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 46.92/47.17          | ~ (v1_relat_1 @ X0))),
% 46.92/47.17      inference('simplify', [status(thm)], ['45'])).
% 46.92/47.17  thf('47', plain,
% 46.92/47.17      (![X17 : $i, X18 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 46.92/47.17      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 46.92/47.17  thf('48', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X0)
% 46.92/47.17          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 46.92/47.17             (k2_relat_1 @ X0)))),
% 46.92/47.17      inference('clc', [status(thm)], ['46', '47'])).
% 46.92/47.17  thf('49', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]:
% 46.92/47.17         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 46.92/47.17          | ~ (v1_relat_1 @ X1)
% 46.92/47.17          | ~ (v1_relat_1 @ X1))),
% 46.92/47.17      inference('sup+', [status(thm)], ['42', '48'])).
% 46.92/47.17  thf('50', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X1)
% 46.92/47.17          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 46.92/47.17      inference('simplify', [status(thm)], ['49'])).
% 46.92/47.17  thf('51', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 46.92/47.17           (k9_relat_1 @ X1 @ X0))
% 46.92/47.17          | ~ (v1_relat_1 @ X1)
% 46.92/47.17          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 46.92/47.17      inference('sup+', [status(thm)], ['41', '50'])).
% 46.92/47.17  thf('52', plain,
% 46.92/47.17      (![X17 : $i, X18 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 46.92/47.17      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 46.92/47.17  thf('53', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X1)
% 46.92/47.17          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 46.92/47.17             (k9_relat_1 @ X1 @ X0)))),
% 46.92/47.17      inference('clc', [status(thm)], ['51', '52'])).
% 46.92/47.17  thf('54', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 46.92/47.17           (k9_relat_1 @ X2 @ X0))
% 46.92/47.17          | ~ (v1_relat_1 @ X2)
% 46.92/47.17          | ~ (v1_relat_1 @ X2))),
% 46.92/47.17      inference('sup+', [status(thm)], ['40', '53'])).
% 46.92/47.17  thf('55', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X2)
% 46.92/47.17          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 46.92/47.17             (k9_relat_1 @ X2 @ X0)))),
% 46.92/47.17      inference('simplify', [status(thm)], ['54'])).
% 46.92/47.17  thf('56', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 46.92/47.17           (k9_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ X1) @ X2))
% 46.92/47.17          | ~ (v1_relat_1 @ X1)
% 46.92/47.17          | ~ (v1_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ X1)))),
% 46.92/47.17      inference('sup+', [status(thm)], ['36', '55'])).
% 46.92/47.17  thf('57', plain,
% 46.92/47.17      (![X19 : $i, X20 : $i]:
% 46.92/47.17         ((v1_relat_1 @ (k8_relat_1 @ X19 @ X20)) | ~ (v1_relat_1 @ X20))),
% 46.92/47.17      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 46.92/47.17  thf('58', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X1)
% 46.92/47.17          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 46.92/47.17             (k9_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ X1) @ X2)))),
% 46.92/47.17      inference('clc', [status(thm)], ['56', '57'])).
% 46.92/47.17  thf('59', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 46.92/47.17           (k9_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X2 @ X0) @ X2) @ X1))
% 46.92/47.17          | ~ (v1_relat_1 @ X2)
% 46.92/47.17          | ~ (v1_relat_1 @ X2))),
% 46.92/47.17      inference('sup+', [status(thm)], ['25', '58'])).
% 46.92/47.17  thf('60', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X2)
% 46.92/47.17          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 46.92/47.17             (k9_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ X2 @ X0) @ X2) @ X1)))),
% 46.92/47.17      inference('simplify', [status(thm)], ['59'])).
% 46.92/47.17  thf('61', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 46.92/47.17           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 46.92/47.17          | ~ (v1_relat_1 @ X1)
% 46.92/47.17          | ~ (v1_relat_1 @ X1))),
% 46.92/47.17      inference('sup+', [status(thm)], ['11', '60'])).
% 46.92/47.17  thf('62', plain,
% 46.92/47.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.92/47.17         (~ (v1_relat_1 @ X1)
% 46.92/47.17          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 46.92/47.17             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))))),
% 46.92/47.17      inference('simplify', [status(thm)], ['61'])).
% 46.92/47.17  thf(t154_relat_1, conjecture,
% 46.92/47.17    (![A:$i,B:$i,C:$i]:
% 46.92/47.17     ( ( v1_relat_1 @ C ) =>
% 46.92/47.17       ( r1_tarski @
% 46.92/47.17         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 46.92/47.17         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 46.92/47.17  thf(zf_stmt_0, negated_conjecture,
% 46.92/47.17    (~( ![A:$i,B:$i,C:$i]:
% 46.92/47.17        ( ( v1_relat_1 @ C ) =>
% 46.92/47.17          ( r1_tarski @
% 46.92/47.17            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 46.92/47.17            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 46.92/47.17    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 46.92/47.17  thf('63', plain,
% 46.92/47.17      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 46.92/47.17          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 46.92/47.17           (k9_relat_1 @ sk_C @ sk_B)))),
% 46.92/47.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.92/47.17  thf('64', plain, (~ (v1_relat_1 @ sk_C)),
% 46.92/47.17      inference('sup-', [status(thm)], ['62', '63'])).
% 46.92/47.17  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 46.92/47.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.92/47.17  thf('66', plain, ($false), inference('demod', [status(thm)], ['64', '65'])).
% 46.92/47.17  
% 46.92/47.17  % SZS output end Refutation
% 46.92/47.17  
% 46.92/47.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
