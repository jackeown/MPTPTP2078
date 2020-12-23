%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SNwDLVubtf

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:56 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  130 (2130 expanded)
%              Number of leaves         :   28 ( 776 expanded)
%              Depth                    :   19
%              Number of atoms          : 1093 (17386 expanded)
%              Number of equality atoms :   97 (1471 expanded)
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

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('10',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X40: $i] :
      ( ( ( k7_relat_1 @ X40 @ ( k1_relat_1 @ X40 ) )
        = X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['18','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('28',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('29',plain,(
    ! [X33: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X33 ) )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X29 ) @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('36',plain,(
    ! [X33: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X33 ) )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('38',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('39',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X34 ) @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k8_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ X22 @ ( k6_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('48',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X34 ) @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('51',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','56','57'])).

thf('59',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('60',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','58','59','60'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('69',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X24 @ X25 ) @ X26 )
        = ( k8_relat_1 @ X24 @ ( k7_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['64','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('81',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('84',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['79','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','58','59','60'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['78','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','58','59','60'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','98'])).

thf('100',plain,(
    $false ),
    inference(simplify,[status(thm)],['99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SNwDLVubtf
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:21:57 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.76/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.95  % Solved by: fo/fo7.sh
% 0.76/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.95  % done 895 iterations in 0.486s
% 0.76/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.95  % SZS output start Refutation
% 0.76/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.95  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.76/0.95  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.76/0.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.95  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.76/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.95  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.76/0.95  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.76/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.95  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/0.95  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.76/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.95  thf(t123_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ B ) =>
% 0.76/0.95       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.76/0.95  thf('0', plain,
% 0.76/0.95      (![X22 : $i, X23 : $i]:
% 0.76/0.95         (((k8_relat_1 @ X23 @ X22) = (k5_relat_1 @ X22 @ (k6_relat_1 @ X23)))
% 0.76/0.95          | ~ (v1_relat_1 @ X22))),
% 0.76/0.95      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.76/0.95  thf(t43_funct_1, conjecture,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.76/0.95       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.76/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.95    (~( ![A:$i,B:$i]:
% 0.76/0.95        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.76/0.95          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.76/0.95    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.76/0.95  thf('1', plain,
% 0.76/0.95      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.76/0.95         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('2', plain,
% 0.76/0.95      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.76/0.95          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.76/0.95        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.95  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.76/0.95  thf('3', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('4', plain,
% 0.76/0.95      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.76/0.95         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['2', '3'])).
% 0.76/0.95  thf(commutativity_k2_tarski, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.76/0.95  thf('5', plain,
% 0.76/0.95      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.76/0.95      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.76/0.95  thf(t12_setfam_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.95  thf('6', plain,
% 0.76/0.95      (![X9 : $i, X10 : $i]:
% 0.76/0.95         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.76/0.95      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.76/0.95  thf('7', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.95      inference('sup+', [status(thm)], ['5', '6'])).
% 0.76/0.95  thf('8', plain,
% 0.76/0.95      (![X9 : $i, X10 : $i]:
% 0.76/0.95         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.76/0.95      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.76/0.95  thf('9', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.95      inference('sup+', [status(thm)], ['7', '8'])).
% 0.76/0.95  thf(t71_relat_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.76/0.95       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.76/0.95  thf('10', plain, (![X31 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X31)) = (X31))),
% 0.76/0.95      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.76/0.95  thf(t98_relat_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ A ) =>
% 0.76/0.95       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.76/0.95  thf('11', plain,
% 0.76/0.95      (![X40 : $i]:
% 0.76/0.95         (((k7_relat_1 @ X40 @ (k1_relat_1 @ X40)) = (X40))
% 0.76/0.95          | ~ (v1_relat_1 @ X40))),
% 0.76/0.95      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.76/0.95  thf('12', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['10', '11'])).
% 0.76/0.95  thf('13', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('14', plain,
% 0.76/0.95      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['12', '13'])).
% 0.76/0.95  thf(t100_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ C ) =>
% 0.76/0.95       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.76/0.95         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.76/0.95  thf('15', plain,
% 0.76/0.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.95         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 0.76/0.95            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 0.76/0.95          | ~ (v1_relat_1 @ X16))),
% 0.76/0.95      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.76/0.95  thf('16', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.76/0.95            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/0.95  thf('17', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('18', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.76/0.95           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.95  thf('19', plain,
% 0.76/0.95      (![X22 : $i, X23 : $i]:
% 0.76/0.95         (((k8_relat_1 @ X23 @ X22) = (k5_relat_1 @ X22 @ (k6_relat_1 @ X23)))
% 0.76/0.95          | ~ (v1_relat_1 @ X22))),
% 0.76/0.95      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.76/0.95  thf(t94_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ B ) =>
% 0.76/0.95       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.76/0.95  thf('20', plain,
% 0.76/0.95      (![X36 : $i, X37 : $i]:
% 0.76/0.95         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 0.76/0.95          | ~ (v1_relat_1 @ X37))),
% 0.76/0.95      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.76/0.95  thf('21', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.76/0.95            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('22', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('23', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('24', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.95  thf('25', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.95  thf('26', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.76/0.95           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.76/0.95      inference('demod', [status(thm)], ['18', '24', '25'])).
% 0.76/0.95  thf('27', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.76/0.95           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['9', '26'])).
% 0.76/0.95  thf('28', plain,
% 0.76/0.95      (![X36 : $i, X37 : $i]:
% 0.76/0.95         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 0.76/0.95          | ~ (v1_relat_1 @ X37))),
% 0.76/0.95      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.76/0.95  thf(t72_relat_1, axiom,
% 0.76/0.95    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.76/0.95  thf('29', plain,
% 0.76/0.95      (![X33 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X33)) = (k6_relat_1 @ X33))),
% 0.76/0.95      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.76/0.95  thf(t54_relat_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ A ) =>
% 0.76/0.95       ( ![B:$i]:
% 0.76/0.95         ( ( v1_relat_1 @ B ) =>
% 0.76/0.95           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.76/0.95             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.76/0.95  thf('30', plain,
% 0.76/0.95      (![X29 : $i, X30 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X29)
% 0.76/0.95          | ((k4_relat_1 @ (k5_relat_1 @ X30 @ X29))
% 0.76/0.95              = (k5_relat_1 @ (k4_relat_1 @ X29) @ (k4_relat_1 @ X30)))
% 0.76/0.95          | ~ (v1_relat_1 @ X30))),
% 0.76/0.95      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.76/0.95  thf('31', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.76/0.95          | ~ (v1_relat_1 @ X1)
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['29', '30'])).
% 0.76/0.95  thf('32', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('33', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.76/0.95          | ~ (v1_relat_1 @ X1))),
% 0.76/0.95      inference('demod', [status(thm)], ['31', '32'])).
% 0.76/0.95  thf('34', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.76/0.95            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.76/0.95               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['28', '33'])).
% 0.76/0.95  thf('35', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.95  thf('36', plain,
% 0.76/0.95      (![X33 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X33)) = (k6_relat_1 @ X33))),
% 0.76/0.95      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.76/0.95  thf('37', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.95  thf('38', plain,
% 0.76/0.95      (![X36 : $i, X37 : $i]:
% 0.76/0.95         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 0.76/0.95          | ~ (v1_relat_1 @ X37))),
% 0.76/0.95      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.76/0.95  thf(t76_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ B ) =>
% 0.76/0.95       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.76/0.95         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.76/0.95  thf('39', plain,
% 0.76/0.95      (![X34 : $i, X35 : $i]:
% 0.76/0.95         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X35) @ X34) @ X34)
% 0.76/0.95          | ~ (v1_relat_1 @ X34))),
% 0.76/0.95      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.76/0.95  thf(t28_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.76/0.95  thf('40', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.76/0.95  thf('41', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X0)
% 0.76/0.95          | ((k3_xboole_0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 0.76/0.95              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['39', '40'])).
% 0.76/0.95  thf('42', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.95      inference('sup+', [status(thm)], ['7', '8'])).
% 0.76/0.95  thf('43', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X0)
% 0.76/0.95          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.76/0.95              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['41', '42'])).
% 0.76/0.95  thf('44', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))
% 0.76/0.95            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.76/0.95          | ~ (v1_relat_1 @ X1)
% 0.76/0.95          | ~ (v1_relat_1 @ X1))),
% 0.76/0.95      inference('sup+', [status(thm)], ['38', '43'])).
% 0.76/0.95  thf('45', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X1)
% 0.76/0.95          | ((k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))
% 0.76/0.95              = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.76/0.95      inference('simplify', [status(thm)], ['44'])).
% 0.76/0.95  thf('46', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((k3_xboole_0 @ (k6_relat_1 @ X1) @ 
% 0.76/0.95            (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['37', '45'])).
% 0.76/0.95  thf('47', plain,
% 0.76/0.95      (![X22 : $i, X23 : $i]:
% 0.76/0.95         (((k8_relat_1 @ X23 @ X22) = (k5_relat_1 @ X22 @ (k6_relat_1 @ X23)))
% 0.76/0.95          | ~ (v1_relat_1 @ X22))),
% 0.76/0.95      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.76/0.95  thf('48', plain,
% 0.76/0.95      (![X34 : $i, X35 : $i]:
% 0.76/0.95         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X35) @ X34) @ X34)
% 0.76/0.95          | ~ (v1_relat_1 @ X34))),
% 0.76/0.95      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.76/0.95  thf('49', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.76/0.95           (k6_relat_1 @ X1))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['47', '48'])).
% 0.76/0.95  thf('50', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('51', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('52', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X1))),
% 0.76/0.95      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.76/0.95  thf('53', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.76/0.95  thf('54', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k3_xboole_0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 0.76/0.95           (k6_relat_1 @ X0)) = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['52', '53'])).
% 0.76/0.95  thf('55', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.95      inference('sup+', [status(thm)], ['7', '8'])).
% 0.76/0.95  thf('56', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 0.76/0.95           (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.76/0.95           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['54', '55'])).
% 0.76/0.95  thf('57', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('58', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.76/0.95           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['46', '56', '57'])).
% 0.76/0.95  thf('59', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('60', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('61', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '35', '36', '58', '59', '60'])).
% 0.76/0.95  thf('62', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['27', '61'])).
% 0.76/0.95  thf('63', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '35', '36', '58', '59', '60'])).
% 0.76/0.95  thf('64', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.76/0.95           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['62', '63'])).
% 0.76/0.95  thf('65', plain,
% 0.76/0.95      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['12', '13'])).
% 0.76/0.95  thf('66', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.95  thf('67', plain,
% 0.76/0.95      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['65', '66'])).
% 0.76/0.95  thf('68', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.95  thf(t140_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ C ) =>
% 0.76/0.95       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.76/0.95         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.76/0.95  thf('69', plain,
% 0.76/0.95      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.95         (((k7_relat_1 @ (k8_relat_1 @ X24 @ X25) @ X26)
% 0.76/0.95            = (k8_relat_1 @ X24 @ (k7_relat_1 @ X25 @ X26)))
% 0.76/0.95          | ~ (v1_relat_1 @ X25))),
% 0.76/0.95      inference('cnf', [status(esa)], [t140_relat_1])).
% 0.76/0.95  thf('70', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         (((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.76/0.95            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['68', '69'])).
% 0.76/0.95  thf('71', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('72', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['70', '71'])).
% 0.76/0.95  thf('73', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.76/0.95           = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['67', '72'])).
% 0.76/0.95  thf('74', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.95  thf('75', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.76/0.95           = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.76/0.95      inference('demod', [status(thm)], ['73', '74'])).
% 0.76/0.95  thf('76', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X0))
% 0.76/0.95           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.76/0.95              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['64', '75'])).
% 0.76/0.95  thf('77', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.76/0.95           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['62', '63'])).
% 0.76/0.95  thf('78', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.76/0.95           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.76/0.95              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['76', '77'])).
% 0.76/0.95  thf('79', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['70', '71'])).
% 0.76/0.95  thf('80', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.95  thf('81', plain,
% 0.76/0.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.95         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 0.76/0.95            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 0.76/0.95          | ~ (v1_relat_1 @ X16))),
% 0.76/0.95      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.76/0.95  thf('82', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.76/0.95            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 0.76/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['80', '81'])).
% 0.76/0.95  thf('83', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.95  thf('84', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.76/0.95  thf('85', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.76/0.95      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.76/0.95  thf('86', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['79', '85'])).
% 0.76/0.95  thf('87', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '35', '36', '58', '59', '60'])).
% 0.76/0.95  thf('88', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         ((k4_relat_1 @ 
% 0.76/0.95           (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.76/0.95           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X2)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['86', '87'])).
% 0.76/0.95  thf('89', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.76/0.95              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['78', '88'])).
% 0.76/0.95  thf('90', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.76/0.95           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '35', '36', '58', '59', '60'])).
% 0.76/0.95  thf('91', plain,
% 0.76/0.95      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['65', '66'])).
% 0.76/0.95  thf('92', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.76/0.95           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.76/0.95  thf('93', plain,
% 0.76/0.95      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.76/0.95         != (k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '92'])).
% 0.76/0.95  thf('94', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.95      inference('sup+', [status(thm)], ['7', '8'])).
% 0.76/0.95  thf('95', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.76/0.95           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.76/0.95  thf('96', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.76/0.95           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['94', '95'])).
% 0.76/0.95  thf('97', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.76/0.95           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.76/0.95  thf('98', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.76/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['96', '97'])).
% 0.76/0.95  thf('99', plain,
% 0.76/0.95      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.76/0.95         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['93', '98'])).
% 0.76/0.95  thf('100', plain, ($false), inference('simplify', [status(thm)], ['99'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
