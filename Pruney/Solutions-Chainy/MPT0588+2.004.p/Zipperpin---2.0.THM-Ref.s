%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqwyf0bWRp

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:30 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 220 expanded)
%              Number of leaves         :   26 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          :  710 (1712 expanded)
%              Number of equality atoms :   52 ( 143 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X27 @ X28 ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k1_relat_1 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('24',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X27 @ X28 ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('25',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('26',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X33 ) @ X34 )
      | ( ( k7_relat_1 @ X33 @ X34 )
        = X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35','40'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','44'])).

thf('46',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['22','47'])).

thf('49',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('50',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X33 ) @ X34 )
      | ( ( k7_relat_1 @ X33 @ X34 )
        = X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t192_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k7_relat_1 @ B @ A )
          = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t192_relat_1])).

thf('57',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('59',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqwyf0bWRp
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:00:08 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.07/1.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.26  % Solved by: fo/fo7.sh
% 1.07/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.26  % done 1383 iterations in 0.791s
% 1.07/1.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.26  % SZS output start Refutation
% 1.07/1.26  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.07/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.26  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.07/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.26  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.07/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.26  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.07/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.26  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.07/1.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.07/1.26  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.07/1.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.26  thf(t100_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ C ) =>
% 1.07/1.26       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.07/1.26         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 1.07/1.26  thf('0', plain,
% 1.07/1.26      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.07/1.26         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 1.07/1.26            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 1.07/1.26          | ~ (v1_relat_1 @ X16))),
% 1.07/1.26      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.07/1.26  thf(t94_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ B ) =>
% 1.07/1.26       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.07/1.26  thf('1', plain,
% 1.07/1.26      (![X31 : $i, X32 : $i]:
% 1.07/1.26         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 1.07/1.26          | ~ (v1_relat_1 @ X32))),
% 1.07/1.26      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.07/1.26  thf(t123_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ B ) =>
% 1.07/1.26       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 1.07/1.26  thf('2', plain,
% 1.07/1.26      (![X19 : $i, X20 : $i]:
% 1.07/1.26         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 1.07/1.26          | ~ (v1_relat_1 @ X19))),
% 1.07/1.26      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.07/1.26  thf('3', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.07/1.26            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.07/1.26          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.07/1.26          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['1', '2'])).
% 1.07/1.26  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.07/1.26  thf('4', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.07/1.26  thf('5', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.07/1.26  thf('6', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.07/1.26           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.07/1.26  thf(t88_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 1.07/1.26  thf('7', plain,
% 1.07/1.26      (![X27 : $i, X28 : $i]:
% 1.07/1.26         ((r1_tarski @ (k7_relat_1 @ X27 @ X28) @ X27) | ~ (v1_relat_1 @ X27))),
% 1.07/1.26      inference('cnf', [status(esa)], [t88_relat_1])).
% 1.07/1.26  thf(t25_relat_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ A ) =>
% 1.07/1.26       ( ![B:$i]:
% 1.07/1.26         ( ( v1_relat_1 @ B ) =>
% 1.07/1.26           ( ( r1_tarski @ A @ B ) =>
% 1.07/1.26             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.07/1.26               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.07/1.26  thf('8', plain,
% 1.07/1.26      (![X23 : $i, X24 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X23)
% 1.07/1.26          | (r1_tarski @ (k1_relat_1 @ X24) @ (k1_relat_1 @ X23))
% 1.07/1.26          | ~ (r1_tarski @ X24 @ X23)
% 1.07/1.26          | ~ (v1_relat_1 @ X24))),
% 1.07/1.26      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.07/1.26  thf('9', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.07/1.26          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 1.07/1.26             (k1_relat_1 @ X0))
% 1.07/1.26          | ~ (v1_relat_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['7', '8'])).
% 1.07/1.26  thf('10', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 1.07/1.26           (k1_relat_1 @ X0))
% 1.07/1.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.07/1.26          | ~ (v1_relat_1 @ X0))),
% 1.07/1.26      inference('simplify', [status(thm)], ['9'])).
% 1.07/1.26  thf('11', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.07/1.26          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.07/1.26          | (r1_tarski @ 
% 1.07/1.26             (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.07/1.26             (k1_relat_1 @ (k6_relat_1 @ X1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['6', '10'])).
% 1.07/1.26  thf('12', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.07/1.26  thf('13', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.07/1.26           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.07/1.26  thf(t71_relat_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.07/1.26       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.07/1.26  thf('14', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 1.07/1.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.26  thf('15', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.07/1.26          | (r1_tarski @ 
% 1.07/1.26             (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1))),
% 1.07/1.26      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 1.07/1.26  thf('16', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.07/1.26           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.07/1.26  thf(t90_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ B ) =>
% 1.07/1.26       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.07/1.26         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.07/1.26  thf('17', plain,
% 1.07/1.26      (![X29 : $i, X30 : $i]:
% 1.07/1.26         (((k1_relat_1 @ (k7_relat_1 @ X29 @ X30))
% 1.07/1.26            = (k3_xboole_0 @ (k1_relat_1 @ X29) @ X30))
% 1.07/1.26          | ~ (v1_relat_1 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.07/1.26  thf('18', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.07/1.26            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 1.07/1.26          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['16', '17'])).
% 1.07/1.26  thf('19', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 1.07/1.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.26  thf('20', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.07/1.26  thf('21', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.07/1.26           = (k3_xboole_0 @ X1 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.07/1.26  thf('22', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.07/1.26          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.07/1.26      inference('demod', [status(thm)], ['15', '21'])).
% 1.07/1.26  thf('23', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.07/1.26           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.07/1.26  thf('24', plain,
% 1.07/1.26      (![X27 : $i, X28 : $i]:
% 1.07/1.26         ((r1_tarski @ (k7_relat_1 @ X27 @ X28) @ X27) | ~ (v1_relat_1 @ X27))),
% 1.07/1.26      inference('cnf', [status(esa)], [t88_relat_1])).
% 1.07/1.26  thf('25', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 1.07/1.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.26  thf(t97_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ B ) =>
% 1.07/1.26       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.07/1.26         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.07/1.26  thf('26', plain,
% 1.07/1.26      (![X33 : $i, X34 : $i]:
% 1.07/1.26         (~ (r1_tarski @ (k1_relat_1 @ X33) @ X34)
% 1.07/1.26          | ((k7_relat_1 @ X33 @ X34) = (X33))
% 1.07/1.26          | ~ (v1_relat_1 @ X33))),
% 1.07/1.26      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.07/1.26  thf('27', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (r1_tarski @ X0 @ X1)
% 1.07/1.26          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.07/1.26          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['25', '26'])).
% 1.07/1.26  thf('28', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.07/1.26  thf('29', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (r1_tarski @ X0 @ X1)
% 1.07/1.26          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 1.07/1.26      inference('demod', [status(thm)], ['27', '28'])).
% 1.07/1.26  thf('30', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.07/1.26           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.07/1.26  thf('31', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (r1_tarski @ X0 @ X1)
% 1.07/1.26          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (k6_relat_1 @ X0)))),
% 1.07/1.26      inference('demod', [status(thm)], ['29', '30'])).
% 1.07/1.26  thf('32', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X0)
% 1.07/1.26          | ((k8_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 1.07/1.26              = (k6_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['24', '31'])).
% 1.07/1.26  thf('33', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.07/1.26           = (k3_xboole_0 @ X1 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.07/1.26  thf('34', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (((k1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.07/1.26            = (k3_xboole_0 @ (k7_relat_1 @ X1 @ X0) @ X1))
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('sup+', [status(thm)], ['32', '33'])).
% 1.07/1.26  thf('35', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 1.07/1.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.26  thf(commutativity_k2_tarski, axiom,
% 1.07/1.26    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.07/1.26  thf('36', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.07/1.26      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.07/1.26  thf(t12_setfam_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.07/1.26  thf('37', plain,
% 1.07/1.26      (![X11 : $i, X12 : $i]:
% 1.07/1.26         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 1.07/1.26      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.07/1.26  thf('38', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.26      inference('sup+', [status(thm)], ['36', '37'])).
% 1.07/1.26  thf('39', plain,
% 1.07/1.26      (![X11 : $i, X12 : $i]:
% 1.07/1.26         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 1.07/1.26      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.07/1.26  thf('40', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.26      inference('sup+', [status(thm)], ['38', '39'])).
% 1.07/1.26  thf('41', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (((k7_relat_1 @ X1 @ X0) = (k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('demod', [status(thm)], ['34', '35', '40'])).
% 1.07/1.26  thf(fc1_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.07/1.26  thf('42', plain,
% 1.07/1.26      (![X14 : $i, X15 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc1_relat_1])).
% 1.07/1.26  thf('43', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.07/1.26          | ~ (v1_relat_1 @ X1)
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('sup+', [status(thm)], ['41', '42'])).
% 1.07/1.26  thf('44', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.07/1.26      inference('simplify', [status(thm)], ['43'])).
% 1.07/1.26  thf('45', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.07/1.26          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['23', '44'])).
% 1.07/1.26  thf('46', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.07/1.26  thf('47', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.07/1.26      inference('demod', [status(thm)], ['45', '46'])).
% 1.07/1.26  thf('48', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.07/1.26      inference('demod', [status(thm)], ['22', '47'])).
% 1.07/1.26  thf('49', plain,
% 1.07/1.26      (![X29 : $i, X30 : $i]:
% 1.07/1.26         (((k1_relat_1 @ (k7_relat_1 @ X29 @ X30))
% 1.07/1.26            = (k3_xboole_0 @ (k1_relat_1 @ X29) @ X30))
% 1.07/1.26          | ~ (v1_relat_1 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.07/1.26  thf('50', plain,
% 1.07/1.26      (![X33 : $i, X34 : $i]:
% 1.07/1.26         (~ (r1_tarski @ (k1_relat_1 @ X33) @ X34)
% 1.07/1.26          | ((k7_relat_1 @ X33 @ X34) = (X33))
% 1.07/1.26          | ~ (v1_relat_1 @ X33))),
% 1.07/1.26      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.07/1.26  thf('51', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2)
% 1.07/1.26          | ~ (v1_relat_1 @ X1)
% 1.07/1.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.07/1.26          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.07/1.26              = (k7_relat_1 @ X1 @ X0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['49', '50'])).
% 1.07/1.26  thf('52', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.07/1.26            = (k7_relat_1 @ X0 @ X1))
% 1.07/1.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.07/1.26          | ~ (v1_relat_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['48', '51'])).
% 1.07/1.26  thf('53', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.07/1.26      inference('simplify', [status(thm)], ['43'])).
% 1.07/1.26  thf('54', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X0)
% 1.07/1.26          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.07/1.26              = (k7_relat_1 @ X0 @ X1)))),
% 1.07/1.26      inference('clc', [status(thm)], ['52', '53'])).
% 1.07/1.26  thf('55', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (((k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 1.07/1.26            = (k7_relat_1 @ X0 @ X1))
% 1.07/1.26          | ~ (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X0))),
% 1.07/1.26      inference('sup+', [status(thm)], ['0', '54'])).
% 1.07/1.26  thf('56', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X0)
% 1.07/1.26          | ((k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 1.07/1.26              = (k7_relat_1 @ X0 @ X1)))),
% 1.07/1.26      inference('simplify', [status(thm)], ['55'])).
% 1.07/1.26  thf(t192_relat_1, conjecture,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ B ) =>
% 1.07/1.26       ( ( k7_relat_1 @ B @ A ) =
% 1.07/1.26         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 1.07/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.26    (~( ![A:$i,B:$i]:
% 1.07/1.26        ( ( v1_relat_1 @ B ) =>
% 1.07/1.26          ( ( k7_relat_1 @ B @ A ) =
% 1.07/1.26            ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )),
% 1.07/1.26    inference('cnf.neg', [status(esa)], [t192_relat_1])).
% 1.07/1.26  thf('57', plain,
% 1.07/1.26      (((k7_relat_1 @ sk_B @ sk_A)
% 1.07/1.26         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('58', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.26      inference('sup+', [status(thm)], ['38', '39'])).
% 1.07/1.26  thf('59', plain,
% 1.07/1.26      (((k7_relat_1 @ sk_B @ sk_A)
% 1.07/1.26         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 1.07/1.26      inference('demod', [status(thm)], ['57', '58'])).
% 1.07/1.26  thf('60', plain,
% 1.07/1.26      ((((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))
% 1.07/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['56', '59'])).
% 1.07/1.26  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('62', plain,
% 1.07/1.26      (((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['60', '61'])).
% 1.07/1.26  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 1.07/1.26  
% 1.07/1.26  % SZS output end Refutation
% 1.07/1.26  
% 1.07/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
