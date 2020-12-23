%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CpIa4MYjfu

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:56 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 264 expanded)
%              Number of leaves         :   23 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  813 (2002 expanded)
%              Number of equality atoms :   57 ( 144 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k8_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ X22 @ ( k6_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k8_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ X22 @ ( k6_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X24 @ X25 ) @ X26 )
        = ( k8_relat_1 @ X24 @ ( k7_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('19',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['14','20'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('22',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('23',plain,(
    ! [X39: $i] :
      ( ( ( k7_relat_1 @ X39 @ ( k1_relat_1 @ X39 ) )
        = X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k8_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ X22 @ ( k6_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('39',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('40',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) ) @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k2_relat_1 @ X28 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('50',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('60',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['48','58','59','60'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('62',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X34 )
      | ( ( k5_relat_1 @ X33 @ ( k6_relat_1 @ X34 ) )
        = X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['38','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['37','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','71'])).

thf('73',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','72'])).

thf('74',plain,(
    $false ),
    inference(simplify,[status(thm)],['73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CpIa4MYjfu
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.13/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.13/1.34  % Solved by: fo/fo7.sh
% 1.13/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.34  % done 1321 iterations in 0.882s
% 1.13/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.13/1.34  % SZS output start Refutation
% 1.13/1.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.13/1.34  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.13/1.34  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.13/1.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.13/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.13/1.34  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.13/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.34  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.34  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.13/1.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.13/1.34  thf(t123_relat_1, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( v1_relat_1 @ B ) =>
% 1.13/1.34       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 1.13/1.34  thf('0', plain,
% 1.13/1.34      (![X22 : $i, X23 : $i]:
% 1.13/1.34         (((k8_relat_1 @ X23 @ X22) = (k5_relat_1 @ X22 @ (k6_relat_1 @ X23)))
% 1.13/1.34          | ~ (v1_relat_1 @ X22))),
% 1.13/1.34      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.13/1.34  thf(t43_funct_1, conjecture,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.13/1.34       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.13/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.34    (~( ![A:$i,B:$i]:
% 1.13/1.34        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.13/1.34          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.13/1.34    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 1.13/1.34  thf('1', plain,
% 1.13/1.34      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 1.13/1.34         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.13/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.34  thf('2', plain,
% 1.13/1.34      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.13/1.34          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 1.13/1.34        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['0', '1'])).
% 1.13/1.34  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.13/1.34  thf('3', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('4', plain,
% 1.13/1.34      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.13/1.34         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.13/1.34      inference('demod', [status(thm)], ['2', '3'])).
% 1.13/1.34  thf('5', plain,
% 1.13/1.34      (![X22 : $i, X23 : $i]:
% 1.13/1.34         (((k8_relat_1 @ X23 @ X22) = (k5_relat_1 @ X22 @ (k6_relat_1 @ X23)))
% 1.13/1.34          | ~ (v1_relat_1 @ X22))),
% 1.13/1.34      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.13/1.34  thf(t94_relat_1, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( v1_relat_1 @ B ) =>
% 1.13/1.34       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.13/1.34  thf('6', plain,
% 1.13/1.34      (![X35 : $i, X36 : $i]:
% 1.13/1.34         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 1.13/1.34          | ~ (v1_relat_1 @ X36))),
% 1.13/1.34      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.13/1.34  thf('7', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.13/1.34            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.13/1.34      inference('sup+', [status(thm)], ['5', '6'])).
% 1.13/1.34  thf('8', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('9', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('10', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.13/1.34  thf(t140_relat_1, axiom,
% 1.13/1.34    (![A:$i,B:$i,C:$i]:
% 1.13/1.34     ( ( v1_relat_1 @ C ) =>
% 1.13/1.34       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 1.13/1.34         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 1.13/1.34  thf('11', plain,
% 1.13/1.34      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.13/1.34         (((k7_relat_1 @ (k8_relat_1 @ X24 @ X25) @ X26)
% 1.13/1.34            = (k8_relat_1 @ X24 @ (k7_relat_1 @ X25 @ X26)))
% 1.13/1.34          | ~ (v1_relat_1 @ X25))),
% 1.13/1.34      inference('cnf', [status(esa)], [t140_relat_1])).
% 1.13/1.34  thf('12', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.34         (((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 1.13/1.34            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.13/1.34      inference('sup+', [status(thm)], ['10', '11'])).
% 1.13/1.34  thf('13', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('14', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 1.13/1.34           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.13/1.34      inference('demod', [status(thm)], ['12', '13'])).
% 1.13/1.34  thf('15', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.13/1.34  thf(t100_relat_1, axiom,
% 1.13/1.34    (![A:$i,B:$i,C:$i]:
% 1.13/1.34     ( ( v1_relat_1 @ C ) =>
% 1.13/1.34       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.13/1.34         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 1.13/1.34  thf('16', plain,
% 1.13/1.34      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.34         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 1.13/1.34            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 1.13/1.34          | ~ (v1_relat_1 @ X16))),
% 1.13/1.34      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.13/1.34  thf('17', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.34         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 1.13/1.34            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.13/1.34      inference('sup+', [status(thm)], ['15', '16'])).
% 1.13/1.34  thf('18', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.13/1.34  thf('19', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('20', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 1.13/1.34      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.13/1.34  thf('21', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.34         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.13/1.34      inference('sup+', [status(thm)], ['14', '20'])).
% 1.13/1.34  thf(t71_relat_1, axiom,
% 1.13/1.34    (![A:$i]:
% 1.13/1.34     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.13/1.34       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.13/1.34  thf('22', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 1.13/1.34      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.13/1.34  thf(t98_relat_1, axiom,
% 1.13/1.34    (![A:$i]:
% 1.13/1.34     ( ( v1_relat_1 @ A ) =>
% 1.13/1.34       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 1.13/1.34  thf('23', plain,
% 1.13/1.34      (![X39 : $i]:
% 1.13/1.34         (((k7_relat_1 @ X39 @ (k1_relat_1 @ X39)) = (X39))
% 1.13/1.34          | ~ (v1_relat_1 @ X39))),
% 1.13/1.34      inference('cnf', [status(esa)], [t98_relat_1])).
% 1.13/1.34  thf('24', plain,
% 1.13/1.34      (![X0 : $i]:
% 1.13/1.34         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('sup+', [status(thm)], ['22', '23'])).
% 1.13/1.34  thf('25', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('26', plain,
% 1.13/1.34      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 1.13/1.34      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.34  thf('27', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.13/1.34  thf('28', plain,
% 1.13/1.34      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 1.13/1.34      inference('demod', [status(thm)], ['26', '27'])).
% 1.13/1.34  thf('29', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.13/1.34           (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.13/1.34      inference('sup+', [status(thm)], ['21', '28'])).
% 1.13/1.34  thf('30', plain,
% 1.13/1.34      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 1.13/1.34      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.34  thf('31', plain,
% 1.13/1.34      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.34         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 1.13/1.34            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 1.13/1.34          | ~ (v1_relat_1 @ X16))),
% 1.13/1.34      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.13/1.34  thf('32', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.13/1.34            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('sup+', [status(thm)], ['30', '31'])).
% 1.13/1.34  thf('33', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('34', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.13/1.34           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.13/1.34      inference('demod', [status(thm)], ['32', '33'])).
% 1.13/1.34  thf('35', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.13/1.34  thf('36', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.13/1.34  thf('37', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 1.13/1.34           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 1.13/1.34      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.13/1.34  thf('38', plain,
% 1.13/1.34      (![X22 : $i, X23 : $i]:
% 1.13/1.34         (((k8_relat_1 @ X23 @ X22) = (k5_relat_1 @ X22 @ (k6_relat_1 @ X23)))
% 1.13/1.34          | ~ (v1_relat_1 @ X22))),
% 1.13/1.34      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.13/1.34  thf('39', plain,
% 1.13/1.34      (![X35 : $i, X36 : $i]:
% 1.13/1.34         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 1.13/1.34          | ~ (v1_relat_1 @ X36))),
% 1.13/1.34      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.13/1.34  thf(t76_relat_1, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( v1_relat_1 @ B ) =>
% 1.13/1.34       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 1.13/1.34         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 1.13/1.34  thf('40', plain,
% 1.13/1.34      (![X31 : $i, X32 : $i]:
% 1.13/1.34         ((r1_tarski @ (k5_relat_1 @ X31 @ (k6_relat_1 @ X32)) @ X31)
% 1.13/1.34          | ~ (v1_relat_1 @ X31))),
% 1.13/1.34      inference('cnf', [status(esa)], [t76_relat_1])).
% 1.13/1.34  thf('41', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 1.13/1.34           (k6_relat_1 @ X0))
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('sup+', [status(thm)], ['39', '40'])).
% 1.13/1.34  thf('42', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('43', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('44', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 1.13/1.34      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.13/1.34  thf('45', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.13/1.34  thf('46', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 1.13/1.34      inference('demod', [status(thm)], ['44', '45'])).
% 1.13/1.34  thf(t25_relat_1, axiom,
% 1.13/1.34    (![A:$i]:
% 1.13/1.34     ( ( v1_relat_1 @ A ) =>
% 1.13/1.34       ( ![B:$i]:
% 1.13/1.34         ( ( v1_relat_1 @ B ) =>
% 1.13/1.34           ( ( r1_tarski @ A @ B ) =>
% 1.13/1.34             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.13/1.34               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.13/1.34  thf('47', plain,
% 1.13/1.34      (![X27 : $i, X28 : $i]:
% 1.13/1.34         (~ (v1_relat_1 @ X27)
% 1.13/1.34          | (r1_tarski @ (k2_relat_1 @ X28) @ (k2_relat_1 @ X27))
% 1.13/1.34          | ~ (r1_tarski @ X28 @ X27)
% 1.13/1.34          | ~ (v1_relat_1 @ X28))),
% 1.13/1.34      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.13/1.34  thf('48', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34          | (r1_tarski @ 
% 1.13/1.34             (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 1.13/1.34             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('sup-', [status(thm)], ['46', '47'])).
% 1.13/1.34  thf('49', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.13/1.34  thf('50', plain,
% 1.13/1.34      (![X35 : $i, X36 : $i]:
% 1.13/1.34         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 1.13/1.34          | ~ (v1_relat_1 @ X36))),
% 1.13/1.34      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.13/1.34  thf(dt_k5_relat_1, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.13/1.34       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.13/1.34  thf('51', plain,
% 1.13/1.34      (![X11 : $i, X12 : $i]:
% 1.13/1.34         (~ (v1_relat_1 @ X11)
% 1.13/1.34          | ~ (v1_relat_1 @ X12)
% 1.13/1.34          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.13/1.34  thf('52', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.13/1.34          | ~ (v1_relat_1 @ X1)
% 1.13/1.34          | ~ (v1_relat_1 @ X1)
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('sup+', [status(thm)], ['50', '51'])).
% 1.13/1.34  thf('53', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('54', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.13/1.34          | ~ (v1_relat_1 @ X1)
% 1.13/1.34          | ~ (v1_relat_1 @ X1))),
% 1.13/1.34      inference('demod', [status(thm)], ['52', '53'])).
% 1.13/1.34  thf('55', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.13/1.34      inference('simplify', [status(thm)], ['54'])).
% 1.13/1.34  thf('56', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.13/1.34      inference('sup+', [status(thm)], ['49', '55'])).
% 1.13/1.34  thf('57', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('58', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['56', '57'])).
% 1.13/1.34  thf('59', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 1.13/1.34      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.13/1.34  thf('60', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.13/1.34      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.13/1.34  thf('61', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)),
% 1.13/1.34      inference('demod', [status(thm)], ['48', '58', '59', '60'])).
% 1.13/1.34  thf(t79_relat_1, axiom,
% 1.13/1.34    (![A:$i,B:$i]:
% 1.13/1.34     ( ( v1_relat_1 @ B ) =>
% 1.13/1.34       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.13/1.34         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.13/1.34  thf('62', plain,
% 1.13/1.34      (![X33 : $i, X34 : $i]:
% 1.13/1.34         (~ (r1_tarski @ (k2_relat_1 @ X33) @ X34)
% 1.13/1.34          | ((k5_relat_1 @ X33 @ (k6_relat_1 @ X34)) = (X33))
% 1.13/1.34          | ~ (v1_relat_1 @ X33))),
% 1.13/1.34      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.13/1.34  thf('63', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34          | ((k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 1.13/1.34              (k6_relat_1 @ X0)) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.13/1.34      inference('sup-', [status(thm)], ['61', '62'])).
% 1.13/1.34  thf('64', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['56', '57'])).
% 1.13/1.34  thf('65', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 1.13/1.34           (k6_relat_1 @ X0)) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['63', '64'])).
% 1.13/1.34  thf('66', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.13/1.34      inference('sup+', [status(thm)], ['38', '65'])).
% 1.13/1.34  thf('67', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['56', '57'])).
% 1.13/1.34  thf('68', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['66', '67'])).
% 1.13/1.34  thf('69', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.13/1.34           (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.13/1.34      inference('sup+', [status(thm)], ['37', '68'])).
% 1.13/1.34  thf('70', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 1.13/1.34           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 1.13/1.34      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.13/1.34  thf('71', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.13/1.34           (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('demod', [status(thm)], ['69', '70'])).
% 1.13/1.34  thf('72', plain,
% 1.13/1.34      (![X0 : $i, X1 : $i]:
% 1.13/1.34         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.13/1.34           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.13/1.34      inference('sup+', [status(thm)], ['29', '71'])).
% 1.13/1.34  thf('73', plain,
% 1.13/1.34      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.13/1.34         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 1.13/1.34      inference('demod', [status(thm)], ['4', '72'])).
% 1.13/1.34  thf('74', plain, ($false), inference('simplify', [status(thm)], ['73'])).
% 1.13/1.34  
% 1.13/1.34  % SZS output end Refutation
% 1.13/1.34  
% 1.13/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
