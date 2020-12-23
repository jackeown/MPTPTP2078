%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OIwSI1Ugux

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:06 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 207 expanded)
%              Number of leaves         :   26 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  791 (1760 expanded)
%              Number of equality atoms :   53 ( 108 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k8_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X46: $i] :
      ( ( ( k7_relat_1 @ X46 @ ( k1_relat_1 @ X46 ) )
        = X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k8_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('15',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k7_relat_1 @ X45 @ X44 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('18',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['13','19','20'])).

thf('22',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k7_relat_1 @ X45 @ X44 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('23',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X40 @ ( k6_relat_1 @ X41 ) ) @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('26',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k2_relat_1 @ X34 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('33',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k7_relat_1 @ X45 @ X44 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('43',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['31','41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','44'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ( ( k8_relat_1 @ X27 @ X26 )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X28 @ X29 ) @ X30 )
        = ( k8_relat_1 @ X28 @ ( k7_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('55',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('58',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('62',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X42 @ X43 ) ) @ X43 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('65',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ( ( k8_relat_1 @ X27 @ X26 )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48','60','72'])).

thf('74',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','73'])).

thf('75',plain,(
    $false ),
    inference(simplify,[status(thm)],['74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OIwSI1Ugux
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 311 iterations in 0.283s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.73  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.55/0.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.55/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.55/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.73  thf(t123_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ B ) =>
% 0.55/0.73       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.55/0.73  thf('0', plain,
% 0.55/0.73      (![X24 : $i, X25 : $i]:
% 0.55/0.73         (((k8_relat_1 @ X25 @ X24) = (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)))
% 0.55/0.73          | ~ (v1_relat_1 @ X24))),
% 0.55/0.73      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.55/0.73  thf(t43_funct_1, conjecture,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.55/0.73       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i,B:$i]:
% 0.55/0.73        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.55/0.73          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.55/0.73         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('2', plain,
% 0.55/0.73      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.55/0.73          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.55/0.73        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.55/0.73  thf(fc24_relat_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.55/0.73       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.55/0.73       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.55/0.73  thf('3', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.73  thf('4', plain,
% 0.55/0.73      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.55/0.73         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.55/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.55/0.73  thf(t71_relat_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.55/0.73       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.55/0.73  thf('5', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.55/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.55/0.73  thf(t98_relat_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ A ) =>
% 0.55/0.73       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.55/0.73  thf('6', plain,
% 0.55/0.73      (![X46 : $i]:
% 0.55/0.73         (((k7_relat_1 @ X46 @ (k1_relat_1 @ X46)) = (X46))
% 0.55/0.74          | ~ (v1_relat_1 @ X46))),
% 0.55/0.74      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['5', '6'])).
% 0.55/0.74  thf('8', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('9', plain,
% 0.55/0.74      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['7', '8'])).
% 0.55/0.74  thf(t100_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ C ) =>
% 0.55/0.74       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.55/0.74         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.74         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 0.55/0.74            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 0.55/0.74          | ~ (v1_relat_1 @ X18))),
% 0.55/0.74      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.55/0.74            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['9', '10'])).
% 0.55/0.74  thf('12', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.55/0.74           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.55/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      (![X24 : $i, X25 : $i]:
% 0.55/0.74         (((k8_relat_1 @ X25 @ X24) = (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)))
% 0.55/0.74          | ~ (v1_relat_1 @ X24))),
% 0.55/0.74      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.55/0.74  thf(t94_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ B ) =>
% 0.55/0.74       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (![X44 : $i, X45 : $i]:
% 0.55/0.74         (((k7_relat_1 @ X45 @ X44) = (k5_relat_1 @ (k6_relat_1 @ X44) @ X45))
% 0.55/0.74          | ~ (v1_relat_1 @ X45))),
% 0.55/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.55/0.74  thf('16', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.55/0.74            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.55/0.74  thf('17', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('18', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.55/0.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.55/0.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.55/0.74  thf('21', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.55/0.74           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.55/0.74      inference('demod', [status(thm)], ['13', '19', '20'])).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      (![X44 : $i, X45 : $i]:
% 0.55/0.74         (((k7_relat_1 @ X45 @ X44) = (k5_relat_1 @ (k6_relat_1 @ X44) @ X45))
% 0.55/0.74          | ~ (v1_relat_1 @ X45))),
% 0.55/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.55/0.74  thf(t76_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ B ) =>
% 0.55/0.74       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.55/0.74         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      (![X40 : $i, X41 : $i]:
% 0.55/0.74         ((r1_tarski @ (k5_relat_1 @ X40 @ (k6_relat_1 @ X41)) @ X40)
% 0.55/0.74          | ~ (v1_relat_1 @ X40))),
% 0.55/0.74      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.55/0.74           (k6_relat_1 @ X0))
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['22', '23'])).
% 0.55/0.74  thf('25', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('26', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('27', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.55/0.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['27', '28'])).
% 0.55/0.74  thf(t25_relat_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( v1_relat_1 @ B ) =>
% 0.55/0.74           ( ( r1_tarski @ A @ B ) =>
% 0.55/0.74             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.55/0.74               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      (![X33 : $i, X34 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X33)
% 0.55/0.74          | (r1_tarski @ (k2_relat_1 @ X34) @ (k2_relat_1 @ X33))
% 0.55/0.74          | ~ (r1_tarski @ X34 @ X33)
% 0.55/0.74          | ~ (v1_relat_1 @ X34))),
% 0.55/0.74      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.55/0.74  thf('31', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.55/0.74          | (r1_tarski @ 
% 0.55/0.74             (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.55/0.74             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.55/0.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      (![X44 : $i, X45 : $i]:
% 0.55/0.74         (((k7_relat_1 @ X45 @ X44) = (k5_relat_1 @ (k6_relat_1 @ X44) @ X45))
% 0.55/0.74          | ~ (v1_relat_1 @ X45))),
% 0.55/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.55/0.74  thf(dt_k5_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.55/0.74       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X16)
% 0.55/0.74          | ~ (v1_relat_1 @ X17)
% 0.55/0.74          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.55/0.74          | ~ (v1_relat_1 @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['33', '34'])).
% 0.55/0.74  thf('36', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('37', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.55/0.74          | ~ (v1_relat_1 @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ X1))),
% 0.55/0.74      inference('demod', [status(thm)], ['35', '36'])).
% 0.55/0.74  thf('38', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.55/0.74      inference('simplify', [status(thm)], ['37'])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['32', '38'])).
% 0.55/0.74  thf('40', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.55/0.74  thf('42', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.55/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.55/0.74  thf('43', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)),
% 0.55/0.74      inference('demod', [status(thm)], ['31', '41', '42', '43'])).
% 0.55/0.74  thf('45', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.55/0.74          (k3_xboole_0 @ X1 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['21', '44'])).
% 0.55/0.74  thf(t125_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ B ) =>
% 0.55/0.74       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.55/0.74         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.55/0.74  thf('46', plain,
% 0.55/0.74      (![X26 : $i, X27 : $i]:
% 0.55/0.74         (~ (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 0.55/0.74          | ((k8_relat_1 @ X27 @ X26) = (X26))
% 0.55/0.74          | ~ (v1_relat_1 @ X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.55/0.74  thf('47', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.55/0.74          | ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.55/0.74              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.55/0.74              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['45', '46'])).
% 0.55/0.74  thf('48', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.55/0.74  thf('49', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.55/0.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.55/0.74  thf(t140_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ C ) =>
% 0.55/0.74       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.55/0.74         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.55/0.74  thf('50', plain,
% 0.55/0.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.74         (((k7_relat_1 @ (k8_relat_1 @ X28 @ X29) @ X30)
% 0.55/0.74            = (k8_relat_1 @ X28 @ (k7_relat_1 @ X29 @ X30)))
% 0.55/0.74          | ~ (v1_relat_1 @ X29))),
% 0.55/0.74      inference('cnf', [status(esa)], [t140_relat_1])).
% 0.55/0.74  thf('51', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         (((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.55/0.74            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['49', '50'])).
% 0.55/0.74  thf('52', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('53', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.55/0.74           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.55/0.74      inference('demod', [status(thm)], ['51', '52'])).
% 0.55/0.74  thf('54', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.55/0.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.55/0.74  thf('55', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.74         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 0.55/0.74            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 0.55/0.74          | ~ (v1_relat_1 @ X18))),
% 0.55/0.74      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.55/0.74  thf('56', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.55/0.74            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['54', '55'])).
% 0.55/0.74  thf('57', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.55/0.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.55/0.74  thf('58', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('59', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.55/0.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.55/0.74      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.55/0.74  thf('60', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.55/0.74           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.55/0.74      inference('sup+', [status(thm)], ['53', '59'])).
% 0.55/0.74  thf('61', plain,
% 0.55/0.74      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['7', '8'])).
% 0.55/0.74  thf(t87_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ B ) =>
% 0.55/0.74       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.55/0.74  thf('62', plain,
% 0.55/0.74      (![X42 : $i, X43 : $i]:
% 0.55/0.74         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X42 @ X43)) @ X43)
% 0.55/0.74          | ~ (v1_relat_1 @ X42))),
% 0.55/0.74      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.55/0.74  thf('63', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['61', '62'])).
% 0.55/0.74  thf('64', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.55/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.55/0.74  thf('65', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('66', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.55/0.74      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.55/0.74  thf('67', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.55/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.55/0.74  thf('68', plain,
% 0.55/0.74      (![X26 : $i, X27 : $i]:
% 0.55/0.74         (~ (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 0.55/0.74          | ((k8_relat_1 @ X27 @ X26) = (X26))
% 0.55/0.74          | ~ (v1_relat_1 @ X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.55/0.74  thf('69', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X0 @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.55/0.74          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['67', '68'])).
% 0.55/0.74  thf('70', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.55/0.74  thf('71', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X0 @ X1)
% 0.55/0.74          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['69', '70'])).
% 0.55/0.74  thf('72', plain,
% 0.55/0.74      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['66', '71'])).
% 0.55/0.74  thf('73', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['47', '48', '60', '72'])).
% 0.55/0.74  thf('74', plain,
% 0.55/0.74      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.55/0.74         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['4', '73'])).
% 0.55/0.74  thf('75', plain, ($false), inference('simplify', [status(thm)], ['74'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
