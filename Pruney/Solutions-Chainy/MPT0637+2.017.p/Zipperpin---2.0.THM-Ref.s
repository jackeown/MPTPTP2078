%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T8pdoQVFeD

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:57 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 262 expanded)
%              Number of leaves         :   27 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  884 (1995 expanded)
%              Number of equality atoms :   67 ( 168 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

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
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('6',plain,(
    ! [X52: $i] :
      ( ( ( k5_relat_1 @ X52 @ ( k6_relat_1 @ ( k2_relat_1 @ X52 ) ) )
        = X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X42 @ X41 ) ) @ ( k1_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('17',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X48 ) @ X49 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X49 ) @ X48 )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k8_relat_1 @ X40 @ ( k5_relat_1 @ X39 @ X38 ) )
        = ( k5_relat_1 @ X39 @ ( k8_relat_1 @ X40 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('26',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('34',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X53 ) @ X54 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('39',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('47',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('48',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X42 @ X41 ) ) @ ( k1_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('51',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['45','56'])).

thf('58',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('59',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X50 ) @ X51 )
      | ( ( k5_relat_1 @ X50 @ ( k6_relat_1 @ X51 ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['44','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['39','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('67',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('72',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('73',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','77'])).

thf('79',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('82',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','37','38','68','69','70','80','81','82'])).

thf('84',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','83'])).

thf('85',plain,(
    $false ),
    inference(simplify,[status(thm)],['84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T8pdoQVFeD
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:14:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 488 iterations in 0.236s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.69  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.69  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.69  thf(t94_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      (![X55 : $i, X56 : $i]:
% 0.45/0.69         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 0.45/0.69          | ~ (v1_relat_1 @ X56))),
% 0.45/0.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.45/0.69  thf(t43_funct_1, conjecture,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.45/0.69       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i,B:$i]:
% 0.45/0.69        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.45/0.69          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.45/0.69         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.45/0.69          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.45/0.69        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.69  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.45/0.69  thf('3', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.45/0.69         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.69  thf(t71_relat_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.45/0.69       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.69  thf('5', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.45/0.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.69  thf(t80_relat_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ A ) =>
% 0.45/0.69       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      (![X52 : $i]:
% 0.45/0.69         (((k5_relat_1 @ X52 @ (k6_relat_1 @ (k2_relat_1 @ X52))) = (X52))
% 0.45/0.69          | ~ (v1_relat_1 @ X52))),
% 0.45/0.69      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.45/0.69            = (k6_relat_1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['5', '6'])).
% 0.45/0.69  thf('8', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.45/0.69           = (k6_relat_1 @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.69  thf(t44_relat_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ A ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( v1_relat_1 @ B ) =>
% 0.45/0.69           ( r1_tarski @
% 0.45/0.69             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      (![X41 : $i, X42 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X41)
% 0.45/0.69          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X42 @ X41)) @ 
% 0.45/0.69             (k1_relat_1 @ X42))
% 0.45/0.69          | ~ (v1_relat_1 @ X42))),
% 0.45/0.69      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.45/0.69           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.69  thf('12', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.45/0.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.69  thf('13', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.45/0.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.69  thf('14', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('15', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.45/0.69      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.45/0.69  thf(t77_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.45/0.69         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (![X48 : $i, X49 : $i]:
% 0.45/0.69         (~ (r1_tarski @ (k1_relat_1 @ X48) @ X49)
% 0.45/0.69          | ((k5_relat_1 @ (k6_relat_1 @ X49) @ X48) = (X48))
% 0.45/0.69          | ~ (v1_relat_1 @ X48))),
% 0.45/0.69      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X0)
% 0.45/0.69          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.69  thf(t123_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X36 : $i, X37 : $i]:
% 0.45/0.69         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.45/0.69          | ~ (v1_relat_1 @ X36))),
% 0.45/0.69      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.45/0.69  thf(t139_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ![C:$i]:
% 0.45/0.69         ( ( v1_relat_1 @ C ) =>
% 0.45/0.69           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.45/0.69             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X38)
% 0.45/0.69          | ((k8_relat_1 @ X40 @ (k5_relat_1 @ X39 @ X38))
% 0.45/0.69              = (k5_relat_1 @ X39 @ (k8_relat_1 @ X40 @ X38)))
% 0.45/0.69          | ~ (v1_relat_1 @ X39))),
% 0.45/0.69      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.45/0.69            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['19', '20'])).
% 0.45/0.69  thf('22', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('23', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.45/0.69            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X0)
% 0.45/0.69          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.45/0.69              = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)))))),
% 0.45/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.69  thf('25', plain,
% 0.45/0.69      (![X36 : $i, X37 : $i]:
% 0.45/0.69         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.45/0.69          | ~ (v1_relat_1 @ X36))),
% 0.45/0.69      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      (![X55 : $i, X56 : $i]:
% 0.45/0.69         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 0.45/0.69          | ~ (v1_relat_1 @ X56))),
% 0.45/0.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.69            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.45/0.69  thf('28', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('29', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('30', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.69           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.45/0.69  thf('31', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X0)
% 0.45/0.69          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.45/0.69              = (k5_relat_1 @ X0 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1))))),
% 0.45/0.69      inference('demod', [status(thm)], ['24', '30'])).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k8_relat_1 @ X1 @ 
% 0.45/0.69            (k8_relat_1 @ X0 @ 
% 0.45/0.69             (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))))
% 0.45/0.69            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ 
% 0.45/0.69               (k6_relat_1 @ 
% 0.45/0.69                (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['18', '31'])).
% 0.45/0.69  thf('33', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.45/0.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.69  thf(t90_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.45/0.69         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.69  thf('34', plain,
% 0.45/0.69      (![X53 : $i, X54 : $i]:
% 0.45/0.69         (((k1_relat_1 @ (k7_relat_1 @ X53 @ X54))
% 0.45/0.69            = (k3_xboole_0 @ (k1_relat_1 @ X53) @ X54))
% 0.45/0.69          | ~ (v1_relat_1 @ X53))),
% 0.45/0.69      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.45/0.69  thf('35', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.45/0.69            = (k3_xboole_0 @ X0 @ X1))
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['33', '34'])).
% 0.45/0.69  thf('36', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.45/0.69           = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('38', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.69           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      (![X36 : $i, X37 : $i]:
% 0.45/0.69         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.45/0.69          | ~ (v1_relat_1 @ X36))),
% 0.45/0.69      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.45/0.69  thf(commutativity_k2_tarski, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.45/0.69  thf('40', plain,
% 0.45/0.69      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.69  thf(t12_setfam_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      (![X31 : $i, X32 : $i]:
% 0.45/0.69         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.69  thf('42', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['40', '41'])).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      (![X31 : $i, X32 : $i]:
% 0.45/0.69         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['42', '43'])).
% 0.45/0.69  thf('45', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['42', '43'])).
% 0.45/0.69  thf('46', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.45/0.69           = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      (![X55 : $i, X56 : $i]:
% 0.45/0.69         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 0.45/0.69          | ~ (v1_relat_1 @ X56))),
% 0.45/0.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      (![X41 : $i, X42 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X41)
% 0.45/0.69          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X42 @ X41)) @ 
% 0.45/0.69             (k1_relat_1 @ X42))
% 0.45/0.69          | ~ (v1_relat_1 @ X42))),
% 0.45/0.69      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.45/0.69           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.45/0.69          | ~ (v1_relat_1 @ X1)
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['47', '48'])).
% 0.45/0.69  thf('50', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.45/0.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.69  thf('51', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('52', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ X1)
% 0.45/0.69          | ~ (v1_relat_1 @ X1))),
% 0.45/0.69      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.45/0.69  thf('53', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X1)
% 0.45/0.69          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 0.45/0.69      inference('simplify', [status(thm)], ['52'])).
% 0.45/0.69  thf('54', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['46', '53'])).
% 0.45/0.69  thf('55', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('56', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.69      inference('demod', [status(thm)], ['54', '55'])).
% 0.45/0.69  thf('57', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.45/0.69      inference('sup+', [status(thm)], ['45', '56'])).
% 0.45/0.69  thf('58', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.45/0.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.69  thf(t79_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.45/0.69         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.45/0.69  thf('59', plain,
% 0.45/0.69      (![X50 : $i, X51 : $i]:
% 0.45/0.69         (~ (r1_tarski @ (k2_relat_1 @ X50) @ X51)
% 0.45/0.69          | ((k5_relat_1 @ X50 @ (k6_relat_1 @ X51)) = (X50))
% 0.45/0.69          | ~ (v1_relat_1 @ X50))),
% 0.45/0.69      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.45/0.69  thf('60', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (r1_tarski @ X0 @ X1)
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.45/0.69          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.45/0.69              = (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.69  thf('61', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('62', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (r1_tarski @ X0 @ X1)
% 0.45/0.69          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.45/0.69              = (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.69  thf('63', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.45/0.69           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['57', '62'])).
% 0.45/0.69  thf('64', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.45/0.69           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['44', '63'])).
% 0.45/0.69  thf('65', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.45/0.69            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['39', '64'])).
% 0.45/0.69  thf('66', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.69           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.45/0.69  thf('67', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('68', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.69           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.69      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.45/0.69  thf('69', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.69           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.45/0.69  thf('70', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.69           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.69      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.45/0.69  thf('71', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.69           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.45/0.69  thf('72', plain,
% 0.45/0.69      (![X36 : $i, X37 : $i]:
% 0.45/0.69         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.45/0.69          | ~ (v1_relat_1 @ X36))),
% 0.45/0.69      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.45/0.69  thf(dt_k5_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.45/0.69       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.45/0.69  thf('73', plain,
% 0.45/0.69      (![X33 : $i, X34 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X33)
% 0.45/0.69          | ~ (v1_relat_1 @ X34)
% 0.45/0.69          | (v1_relat_1 @ (k5_relat_1 @ X33 @ X34)))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.69  thf('74', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.45/0.69          | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['72', '73'])).
% 0.45/0.69  thf('75', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('76', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['74', '75'])).
% 0.45/0.69  thf('77', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['76'])).
% 0.45/0.69  thf('78', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['71', '77'])).
% 0.45/0.69  thf('79', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('80', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['78', '79'])).
% 0.45/0.69  thf('81', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.45/0.69           = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('82', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.69  thf('83', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.69           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.45/0.69      inference('demod', [status(thm)],
% 0.45/0.69                ['32', '37', '38', '68', '69', '70', '80', '81', '82'])).
% 0.45/0.69  thf('84', plain,
% 0.45/0.69      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.45/0.69         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.45/0.69      inference('demod', [status(thm)], ['4', '83'])).
% 0.45/0.69  thf('85', plain, ($false), inference('simplify', [status(thm)], ['84'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
