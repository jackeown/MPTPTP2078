%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JjMKhDVpsB

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:05 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  218 (7310 expanded)
%              Number of leaves         :   30 (2678 expanded)
%              Depth                    :   24
%              Number of atoms          : 2035 (59774 expanded)
%              Number of equality atoms :  152 (4426 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ X56 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
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

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ X56 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X49: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('9',plain,(
    ! [X53: $i] :
      ( ( ( k5_relat_1 @ X53 @ ( k6_relat_1 @ ( k2_relat_1 @ X53 ) ) )
        = X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k8_relat_1 @ X40 @ ( k5_relat_1 @ X39 @ X38 ) )
        = ( k5_relat_1 @ X39 @ ( k8_relat_1 @ X40 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('19',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ X56 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['26','36'])).

thf('38',plain,(
    ! [X48: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X54 @ X55 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('40',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X54 @ X55 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X54 ) @ X55 ) ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X54 @ X55 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X54 ) @ X55 ) ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('53',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k8_relat_1 @ X40 @ ( k5_relat_1 @ X39 @ X38 ) )
        = ( k5_relat_1 @ X39 @ ( k8_relat_1 @ X40 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X54 @ X55 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X54 ) @ X55 ) ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('62',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('65',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X51 ) @ X52 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X51 )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ X56 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('68',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','73'])).

thf('75',plain,(
    ! [X48: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('77',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ X56 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','23','24'])).

thf('79',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X46 @ X45 ) @ X47 )
        = ( k5_relat_1 @ X46 @ ( k5_relat_1 @ X45 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X47 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('84',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('88',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('89',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('92',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k8_relat_1 @ X40 @ ( k5_relat_1 @ X39 @ X38 ) )
        = ( k5_relat_1 @ X39 @ ( k8_relat_1 @ X40 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('95',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('96',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['77','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X48: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('102',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('103',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['74','75','76','100','101','102','103'])).

thf('105',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('107',plain,(
    ! [X50: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X50 ) )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('108',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X44 @ X43 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X43 ) @ ( k4_relat_1 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ X56 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('114',plain,(
    ! [X50: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X50 ) )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('115',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X44 @ X43 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X43 ) @ ( k4_relat_1 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X50: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X50 ) )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('122',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('123',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 ) )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['74','75','76','100','101','102','103'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('143',plain,(
    ! [X48: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('144',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X51 ) @ X52 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X51 )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['142','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X50: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X50 ) )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['141','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','140'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('161',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X42 @ X41 ) ) @ ( k2_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X49: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('164',plain,(
    ! [X49: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('165',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('166',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['162','163','164','165','166'])).

thf('168',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X51 ) @ X52 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X51 )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['159','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['173','174','175','178','179','180','181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['155','156','183'])).

thf('185',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','184'])).

thf('186',plain,(
    $false ),
    inference(simplify,[status(thm)],['185'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JjMKhDVpsB
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:49:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.16  % Solved by: fo/fo7.sh
% 0.89/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.16  % done 998 iterations in 0.697s
% 0.89/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.16  % SZS output start Refutation
% 0.89/1.16  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.89/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.16  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.89/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.16  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.89/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.16  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.16  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.89/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.16  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.89/1.16  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.89/1.16  thf(t94_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ B ) =>
% 0.89/1.16       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.89/1.16  thf('0', plain,
% 0.89/1.16      (![X56 : $i, X57 : $i]:
% 0.89/1.16         (((k7_relat_1 @ X57 @ X56) = (k5_relat_1 @ (k6_relat_1 @ X56) @ X57))
% 0.89/1.16          | ~ (v1_relat_1 @ X57))),
% 0.89/1.16      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.89/1.16  thf(t43_funct_1, conjecture,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.89/1.16       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.89/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.16    (~( ![A:$i,B:$i]:
% 0.89/1.16        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.89/1.16          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.89/1.16    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.89/1.16  thf('1', plain,
% 0.89/1.16      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.89/1.16         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf(t12_setfam_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.89/1.16  thf('2', plain,
% 0.89/1.16      (![X31 : $i, X32 : $i]:
% 0.89/1.16         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.89/1.16      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.89/1.16  thf('3', plain,
% 0.89/1.16      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.89/1.16         != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.89/1.16      inference('demod', [status(thm)], ['1', '2'])).
% 0.89/1.16  thf('4', plain,
% 0.89/1.16      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.89/1.16          != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))
% 0.89/1.16        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['0', '3'])).
% 0.89/1.16  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.89/1.16  thf('5', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('6', plain,
% 0.89/1.16      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.89/1.16         != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.89/1.16      inference('demod', [status(thm)], ['4', '5'])).
% 0.89/1.16  thf('7', plain,
% 0.89/1.16      (![X56 : $i, X57 : $i]:
% 0.89/1.16         (((k7_relat_1 @ X57 @ X56) = (k5_relat_1 @ (k6_relat_1 @ X56) @ X57))
% 0.89/1.16          | ~ (v1_relat_1 @ X57))),
% 0.89/1.16      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.89/1.16  thf(t71_relat_1, axiom,
% 0.89/1.16    (![A:$i]:
% 0.89/1.16     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.89/1.16       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.16  thf('8', plain, (![X49 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X49)) = (X49))),
% 0.89/1.16      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.16  thf(t80_relat_1, axiom,
% 0.89/1.16    (![A:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ A ) =>
% 0.89/1.16       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.89/1.16  thf('9', plain,
% 0.89/1.16      (![X53 : $i]:
% 0.89/1.16         (((k5_relat_1 @ X53 @ (k6_relat_1 @ (k2_relat_1 @ X53))) = (X53))
% 0.89/1.16          | ~ (v1_relat_1 @ X53))),
% 0.89/1.16      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.89/1.16  thf('10', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.89/1.16            = (k6_relat_1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['8', '9'])).
% 0.89/1.16  thf('11', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('12', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.89/1.16           = (k6_relat_1 @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['10', '11'])).
% 0.89/1.16  thf(t139_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ B ) =>
% 0.89/1.16       ( ![C:$i]:
% 0.89/1.16         ( ( v1_relat_1 @ C ) =>
% 0.89/1.16           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.89/1.16             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.89/1.16  thf('13', plain,
% 0.89/1.16      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X38)
% 0.89/1.16          | ((k8_relat_1 @ X40 @ (k5_relat_1 @ X39 @ X38))
% 0.89/1.16              = (k5_relat_1 @ X39 @ (k8_relat_1 @ X40 @ X38)))
% 0.89/1.16          | ~ (v1_relat_1 @ X39))),
% 0.89/1.16      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.89/1.16  thf('14', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.89/1.16            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['12', '13'])).
% 0.89/1.16  thf('15', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('16', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('17', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.89/1.16           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.89/1.16      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.89/1.16  thf(t123_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ B ) =>
% 0.89/1.16       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.89/1.16  thf('18', plain,
% 0.89/1.16      (![X36 : $i, X37 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.89/1.16          | ~ (v1_relat_1 @ X36))),
% 0.89/1.16      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.16  thf('19', plain,
% 0.89/1.16      (![X56 : $i, X57 : $i]:
% 0.89/1.16         (((k7_relat_1 @ X57 @ X56) = (k5_relat_1 @ (k6_relat_1 @ X56) @ X57))
% 0.89/1.16          | ~ (v1_relat_1 @ X57))),
% 0.89/1.16      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.89/1.16  thf('20', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['18', '19'])).
% 0.89/1.16  thf('21', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('22', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('23', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.89/1.16  thf('24', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.89/1.16  thf('25', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['17', '23', '24'])).
% 0.89/1.16  thf('26', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['7', '25'])).
% 0.89/1.16  thf('27', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.89/1.16  thf('28', plain,
% 0.89/1.16      (![X36 : $i, X37 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.89/1.16          | ~ (v1_relat_1 @ X36))),
% 0.89/1.16      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.16  thf(dt_k5_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.89/1.16       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.89/1.16  thf('29', plain,
% 0.89/1.16      (![X33 : $i, X34 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X33)
% 0.89/1.16          | ~ (v1_relat_1 @ X34)
% 0.89/1.16          | (v1_relat_1 @ (k5_relat_1 @ X33 @ X34)))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.89/1.16  thf('30', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ X0)
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.89/1.16          | ~ (v1_relat_1 @ X0))),
% 0.89/1.16      inference('sup+', [status(thm)], ['28', '29'])).
% 0.89/1.16  thf('31', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('32', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ X0)
% 0.89/1.16          | ~ (v1_relat_1 @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['30', '31'])).
% 0.89/1.16  thf('33', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.89/1.16      inference('simplify', [status(thm)], ['32'])).
% 0.89/1.16  thf('34', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['27', '33'])).
% 0.89/1.16  thf('35', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('36', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.16  thf('37', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['26', '36'])).
% 0.89/1.16  thf('38', plain, (![X48 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X48)) = (X48))),
% 0.89/1.16      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.16  thf(t90_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ B ) =>
% 0.89/1.16       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.89/1.16         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.89/1.16  thf('39', plain,
% 0.89/1.16      (![X54 : $i, X55 : $i]:
% 0.89/1.16         (((k1_relat_1 @ (k7_relat_1 @ X54 @ X55))
% 0.89/1.16            = (k3_xboole_0 @ (k1_relat_1 @ X54) @ X55))
% 0.89/1.16          | ~ (v1_relat_1 @ X54))),
% 0.89/1.16      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.89/1.16  thf('40', plain,
% 0.89/1.16      (![X31 : $i, X32 : $i]:
% 0.89/1.16         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.89/1.16      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.89/1.16  thf('41', plain,
% 0.89/1.16      (![X54 : $i, X55 : $i]:
% 0.89/1.16         (((k1_relat_1 @ (k7_relat_1 @ X54 @ X55))
% 0.89/1.16            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X54) @ X55)))
% 0.89/1.16          | ~ (v1_relat_1 @ X54))),
% 0.89/1.16      inference('demod', [status(thm)], ['39', '40'])).
% 0.89/1.16  thf('42', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.16            = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['38', '41'])).
% 0.89/1.16  thf('43', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('44', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.16           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.89/1.16      inference('demod', [status(thm)], ['42', '43'])).
% 0.89/1.16  thf('45', plain,
% 0.89/1.16      (![X54 : $i, X55 : $i]:
% 0.89/1.16         (((k1_relat_1 @ (k7_relat_1 @ X54 @ X55))
% 0.89/1.16            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X54) @ X55)))
% 0.89/1.16          | ~ (v1_relat_1 @ X54))),
% 0.89/1.16      inference('demod', [status(thm)], ['39', '40'])).
% 0.89/1.16  thf('46', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         (((k1_relat_1 @ 
% 0.89/1.16            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))
% 0.89/1.16            = (k1_setfam_1 @ 
% 0.89/1.16               (k2_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)))
% 0.89/1.16          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['44', '45'])).
% 0.89/1.16  thf('47', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.16  thf('48', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k1_relat_1 @ 
% 0.89/1.16           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))
% 0.89/1.16           = (k1_setfam_1 @ 
% 0.89/1.16              (k2_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)))),
% 0.89/1.16      inference('demod', [status(thm)], ['46', '47'])).
% 0.89/1.16  thf('49', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k1_setfam_1 @ 
% 0.89/1.16              (k2_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['37', '48'])).
% 0.89/1.16  thf('50', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.16           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.89/1.16      inference('demod', [status(thm)], ['42', '43'])).
% 0.89/1.16  thf('51', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.89/1.16           = (k1_setfam_1 @ 
% 0.89/1.16              (k2_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['49', '50'])).
% 0.89/1.16  thf('52', plain,
% 0.89/1.16      (![X36 : $i, X37 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.89/1.16          | ~ (v1_relat_1 @ X36))),
% 0.89/1.16      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.16  thf('53', plain,
% 0.89/1.16      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X38)
% 0.89/1.16          | ((k8_relat_1 @ X40 @ (k5_relat_1 @ X39 @ X38))
% 0.89/1.16              = (k5_relat_1 @ X39 @ (k8_relat_1 @ X40 @ X38)))
% 0.89/1.16          | ~ (v1_relat_1 @ X39))),
% 0.89/1.16      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.89/1.16  thf('54', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.89/1.16            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.89/1.16          | ~ (v1_relat_1 @ X0)
% 0.89/1.16          | ~ (v1_relat_1 @ X0)
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['52', '53'])).
% 0.89/1.16  thf('55', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('56', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.89/1.16            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.89/1.16          | ~ (v1_relat_1 @ X0)
% 0.89/1.16          | ~ (v1_relat_1 @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['54', '55'])).
% 0.89/1.16  thf('57', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X0)
% 0.89/1.16          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.89/1.16              = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)))))),
% 0.89/1.16      inference('simplify', [status(thm)], ['56'])).
% 0.89/1.16  thf('58', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.89/1.16  thf('59', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X0)
% 0.89/1.16          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.89/1.16              = (k5_relat_1 @ X0 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1))))),
% 0.89/1.16      inference('demod', [status(thm)], ['57', '58'])).
% 0.89/1.16  thf('60', plain,
% 0.89/1.16      (![X54 : $i, X55 : $i]:
% 0.89/1.16         (((k1_relat_1 @ (k7_relat_1 @ X54 @ X55))
% 0.89/1.16            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X54) @ X55)))
% 0.89/1.16          | ~ (v1_relat_1 @ X54))),
% 0.89/1.16      inference('demod', [status(thm)], ['39', '40'])).
% 0.89/1.16  thf(t17_xboole_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.89/1.16  thf('61', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.89/1.16      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.89/1.16  thf('62', plain,
% 0.89/1.16      (![X31 : $i, X32 : $i]:
% 0.89/1.16         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.89/1.16      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.89/1.16  thf('63', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.89/1.16      inference('demod', [status(thm)], ['61', '62'])).
% 0.89/1.16  thf('64', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.89/1.16           (k1_relat_1 @ X1))
% 0.89/1.16          | ~ (v1_relat_1 @ X1))),
% 0.89/1.16      inference('sup+', [status(thm)], ['60', '63'])).
% 0.89/1.16  thf(t77_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ B ) =>
% 0.89/1.16       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.89/1.16         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.89/1.16  thf('65', plain,
% 0.89/1.16      (![X51 : $i, X52 : $i]:
% 0.89/1.16         (~ (r1_tarski @ (k1_relat_1 @ X51) @ X52)
% 0.89/1.16          | ((k5_relat_1 @ (k6_relat_1 @ X52) @ X51) = (X51))
% 0.89/1.16          | ~ (v1_relat_1 @ X51))),
% 0.89/1.16      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.89/1.16  thf('66', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X0)
% 0.89/1.16          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.89/1.16          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 0.89/1.16              (k7_relat_1 @ X0 @ X1)) = (k7_relat_1 @ X0 @ X1)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['64', '65'])).
% 0.89/1.16  thf('67', plain,
% 0.89/1.16      (![X56 : $i, X57 : $i]:
% 0.89/1.16         (((k7_relat_1 @ X57 @ X56) = (k5_relat_1 @ (k6_relat_1 @ X56) @ X57))
% 0.89/1.16          | ~ (v1_relat_1 @ X57))),
% 0.89/1.16      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.89/1.16  thf('68', plain,
% 0.89/1.16      (![X33 : $i, X34 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X33)
% 0.89/1.16          | ~ (v1_relat_1 @ X34)
% 0.89/1.16          | (v1_relat_1 @ (k5_relat_1 @ X33 @ X34)))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.89/1.16  thf('69', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ X1)
% 0.89/1.16          | ~ (v1_relat_1 @ X1)
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['67', '68'])).
% 0.89/1.16  thf('70', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('71', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ X1)
% 0.89/1.16          | ~ (v1_relat_1 @ X1))),
% 0.89/1.16      inference('demod', [status(thm)], ['69', '70'])).
% 0.89/1.16  thf('72', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.89/1.16      inference('simplify', [status(thm)], ['71'])).
% 0.89/1.16  thf('73', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 0.89/1.16            (k7_relat_1 @ X0 @ X1)) = (k7_relat_1 @ X0 @ X1))
% 0.89/1.16          | ~ (v1_relat_1 @ X0))),
% 0.89/1.16      inference('clc', [status(thm)], ['66', '72'])).
% 0.89/1.16  thf('74', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X0 @ 
% 0.89/1.16            (k8_relat_1 @ X1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))
% 0.89/1.16            = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['59', '73'])).
% 0.89/1.16  thf('75', plain, (![X48 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X48)) = (X48))),
% 0.89/1.16      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.16  thf('76', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.89/1.16  thf('77', plain,
% 0.89/1.16      (![X56 : $i, X57 : $i]:
% 0.89/1.16         (((k7_relat_1 @ X57 @ X56) = (k5_relat_1 @ (k6_relat_1 @ X56) @ X57))
% 0.89/1.16          | ~ (v1_relat_1 @ X57))),
% 0.89/1.16      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.89/1.16  thf('78', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['17', '23', '24'])).
% 0.89/1.16  thf('79', plain,
% 0.89/1.16      (![X36 : $i, X37 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.89/1.16          | ~ (v1_relat_1 @ X36))),
% 0.89/1.16      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.16  thf('80', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.89/1.16           = (k6_relat_1 @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['10', '11'])).
% 0.89/1.16  thf(t55_relat_1, axiom,
% 0.89/1.16    (![A:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ A ) =>
% 0.89/1.16       ( ![B:$i]:
% 0.89/1.16         ( ( v1_relat_1 @ B ) =>
% 0.89/1.16           ( ![C:$i]:
% 0.89/1.16             ( ( v1_relat_1 @ C ) =>
% 0.89/1.16               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.89/1.16                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.89/1.16  thf('81', plain,
% 0.89/1.16      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X45)
% 0.89/1.16          | ((k5_relat_1 @ (k5_relat_1 @ X46 @ X45) @ X47)
% 0.89/1.16              = (k5_relat_1 @ X46 @ (k5_relat_1 @ X45 @ X47)))
% 0.89/1.16          | ~ (v1_relat_1 @ X47)
% 0.89/1.16          | ~ (v1_relat_1 @ X46))),
% 0.89/1.16      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.89/1.16  thf('82', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.16            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ X1)
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['80', '81'])).
% 0.89/1.16  thf('83', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('84', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('85', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.16            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.89/1.16          | ~ (v1_relat_1 @ X1))),
% 0.89/1.16      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.89/1.16  thf('86', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.89/1.16            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['79', '85'])).
% 0.89/1.16  thf('87', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.89/1.16  thf('88', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('89', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('90', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.89/1.16           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.89/1.16  thf('91', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('sup+', [status(thm)], ['78', '90'])).
% 0.89/1.16  thf('92', plain,
% 0.89/1.16      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X38)
% 0.89/1.16          | ((k8_relat_1 @ X40 @ (k5_relat_1 @ X39 @ X38))
% 0.89/1.16              = (k5_relat_1 @ X39 @ (k8_relat_1 @ X40 @ X38)))
% 0.89/1.16          | ~ (v1_relat_1 @ X39))),
% 0.89/1.16      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.89/1.16  thf('93', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16               (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['91', '92'])).
% 0.89/1.16  thf('94', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.89/1.16  thf('95', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('96', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('97', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16              (k7_relat_1 @ (k6_relat_1 @ X2) @ X1)))),
% 0.89/1.16      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.89/1.16  thf('98', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['77', '97'])).
% 0.89/1.16  thf('99', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.16  thf('100', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['98', '99'])).
% 0.89/1.16  thf('101', plain, (![X48 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X48)) = (X48))),
% 0.89/1.16      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.16  thf('102', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('103', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('104', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.16      inference('demod', [status(thm)],
% 0.89/1.16                ['74', '75', '76', '100', '101', '102', '103'])).
% 0.89/1.16  thf('105', plain,
% 0.89/1.16      (![X36 : $i, X37 : $i]:
% 0.89/1.16         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.89/1.16          | ~ (v1_relat_1 @ X36))),
% 0.89/1.16      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.16  thf('106', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16              (k7_relat_1 @ (k6_relat_1 @ X2) @ X1)))),
% 0.89/1.16      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.89/1.16  thf(t72_relat_1, axiom,
% 0.89/1.16    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.89/1.16  thf('107', plain,
% 0.89/1.16      (![X50 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X50)) = (k6_relat_1 @ X50))),
% 0.89/1.16      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.89/1.16  thf(t54_relat_1, axiom,
% 0.89/1.16    (![A:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ A ) =>
% 0.89/1.16       ( ![B:$i]:
% 0.89/1.16         ( ( v1_relat_1 @ B ) =>
% 0.89/1.16           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.89/1.16             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.16  thf('108', plain,
% 0.89/1.16      (![X43 : $i, X44 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X43)
% 0.89/1.16          | ((k4_relat_1 @ (k5_relat_1 @ X44 @ X43))
% 0.89/1.16              = (k5_relat_1 @ (k4_relat_1 @ X43) @ (k4_relat_1 @ X44)))
% 0.89/1.16          | ~ (v1_relat_1 @ X44))),
% 0.89/1.16      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.89/1.16  thf('109', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.16            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ X1))),
% 0.89/1.16      inference('sup+', [status(thm)], ['107', '108'])).
% 0.89/1.16  thf('110', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('111', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.16            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.89/1.16          | ~ (v1_relat_1 @ X1))),
% 0.89/1.16      inference('demod', [status(thm)], ['109', '110'])).
% 0.89/1.16  thf('112', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         (((k4_relat_1 @ 
% 0.89/1.16            (k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.89/1.16            = (k5_relat_1 @ 
% 0.89/1.16               (k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1)) @ 
% 0.89/1.16               (k6_relat_1 @ X0)))
% 0.89/1.16          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['106', '111'])).
% 0.89/1.16  thf('113', plain,
% 0.89/1.16      (![X56 : $i, X57 : $i]:
% 0.89/1.16         (((k7_relat_1 @ X57 @ X56) = (k5_relat_1 @ (k6_relat_1 @ X56) @ X57))
% 0.89/1.16          | ~ (v1_relat_1 @ X57))),
% 0.89/1.16      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.89/1.16  thf('114', plain,
% 0.89/1.16      (![X50 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X50)) = (k6_relat_1 @ X50))),
% 0.89/1.16      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.89/1.16  thf('115', plain,
% 0.89/1.16      (![X43 : $i, X44 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X43)
% 0.89/1.16          | ((k4_relat_1 @ (k5_relat_1 @ X44 @ X43))
% 0.89/1.16              = (k5_relat_1 @ (k4_relat_1 @ X43) @ (k4_relat_1 @ X44)))
% 0.89/1.16          | ~ (v1_relat_1 @ X44))),
% 0.89/1.16      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.89/1.16  thf('116', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.16            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.89/1.16          | ~ (v1_relat_1 @ X1)
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['114', '115'])).
% 0.89/1.16  thf('117', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('118', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.16            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.89/1.16          | ~ (v1_relat_1 @ X1))),
% 0.89/1.16      inference('demod', [status(thm)], ['116', '117'])).
% 0.89/1.16  thf('119', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.89/1.16               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['113', '118'])).
% 0.89/1.16  thf('120', plain,
% 0.89/1.16      (![X50 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X50)) = (k6_relat_1 @ X50))),
% 0.89/1.16      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.89/1.16  thf('121', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('sup+', [status(thm)], ['78', '90'])).
% 0.89/1.16  thf('122', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('123', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('124', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.16      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 0.89/1.16  thf('125', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.16  thf('126', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k4_relat_1 @ 
% 0.89/1.16           (k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.89/1.16           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ 
% 0.89/1.16              (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['112', '124', '125'])).
% 0.89/1.16  thf('127', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['98', '99'])).
% 0.89/1.16  thf('128', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k4_relat_1 @ 
% 0.89/1.16           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.89/1.16           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ 
% 0.89/1.16              (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['126', '127'])).
% 0.89/1.16  thf('129', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         (((k4_relat_1 @ 
% 0.89/1.16            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2))
% 0.89/1.16            = (k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.89/1.16          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['105', '128'])).
% 0.89/1.16  thf('130', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['98', '99'])).
% 0.89/1.16  thf('131', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.16  thf('132', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k4_relat_1 @ 
% 0.89/1.16           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2))
% 0.89/1.16           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.89/1.16  thf('133', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1))),
% 0.89/1.16      inference('sup+', [status(thm)], ['104', '132'])).
% 0.89/1.16  thf('134', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.16      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 0.89/1.16  thf('135', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.16      inference('demod', [status(thm)],
% 0.89/1.16                ['74', '75', '76', '100', '101', '102', '103'])).
% 0.89/1.16  thf('136', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.89/1.16  thf('137', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.16           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.89/1.16      inference('demod', [status(thm)], ['42', '43'])).
% 0.89/1.16  thf('138', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['136', '137'])).
% 0.89/1.16  thf('139', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.16           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.89/1.16      inference('demod', [status(thm)], ['42', '43'])).
% 0.89/1.16  thf('140', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.89/1.16           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['138', '139'])).
% 0.89/1.16  thf('141', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.89/1.16           = (k1_setfam_1 @ 
% 0.89/1.16              (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 0.89/1.16      inference('demod', [status(thm)], ['51', '140'])).
% 0.89/1.16  thf('142', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.89/1.16      inference('demod', [status(thm)], ['61', '62'])).
% 0.89/1.16  thf('143', plain, (![X48 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X48)) = (X48))),
% 0.89/1.16      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.16  thf('144', plain,
% 0.89/1.16      (![X51 : $i, X52 : $i]:
% 0.89/1.16         (~ (r1_tarski @ (k1_relat_1 @ X51) @ X52)
% 0.89/1.16          | ((k5_relat_1 @ (k6_relat_1 @ X52) @ X51) = (X51))
% 0.89/1.16          | ~ (v1_relat_1 @ X51))),
% 0.89/1.16      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.89/1.16  thf('145', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (~ (r1_tarski @ X0 @ X1)
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.16          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.89/1.16              = (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['143', '144'])).
% 0.89/1.16  thf('146', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('147', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (~ (r1_tarski @ X0 @ X1)
% 0.89/1.16          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.89/1.16              = (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['145', '146'])).
% 0.89/1.16  thf('148', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('sup+', [status(thm)], ['78', '90'])).
% 0.89/1.16  thf('149', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (~ (r1_tarski @ X0 @ X1)
% 0.89/1.16          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['147', '148'])).
% 0.89/1.16  thf('150', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.89/1.16           X0) = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.89/1.16      inference('sup-', [status(thm)], ['142', '149'])).
% 0.89/1.16  thf('151', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.16      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 0.89/1.16  thf('152', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k4_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.89/1.16              (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.89/1.16      inference('sup+', [status(thm)], ['150', '151'])).
% 0.89/1.16  thf('153', plain,
% 0.89/1.16      (![X50 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X50)) = (k6_relat_1 @ X50))),
% 0.89/1.16      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.89/1.16  thf('154', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.89/1.16              (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.89/1.16      inference('demod', [status(thm)], ['152', '153'])).
% 0.89/1.16  thf('155', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k6_relat_1 @ 
% 0.89/1.16           (k1_setfam_1 @ 
% 0.89/1.16            (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16              (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.89/1.16      inference('sup+', [status(thm)], ['141', '154'])).
% 0.89/1.16  thf('156', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.89/1.16           = (k1_setfam_1 @ 
% 0.89/1.16              (k2_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 0.89/1.16      inference('demod', [status(thm)], ['51', '140'])).
% 0.89/1.16  thf('157', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.89/1.16  thf('158', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.16      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 0.89/1.16  thf('159', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('sup+', [status(thm)], ['157', '158'])).
% 0.89/1.16  thf('160', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.89/1.16           = (k6_relat_1 @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['10', '11'])).
% 0.89/1.16  thf(t45_relat_1, axiom,
% 0.89/1.16    (![A:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ A ) =>
% 0.89/1.16       ( ![B:$i]:
% 0.89/1.16         ( ( v1_relat_1 @ B ) =>
% 0.89/1.16           ( r1_tarski @
% 0.89/1.16             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.89/1.16  thf('161', plain,
% 0.89/1.16      (![X41 : $i, X42 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X41)
% 0.89/1.16          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X42 @ X41)) @ 
% 0.89/1.16             (k2_relat_1 @ X41))
% 0.89/1.16          | ~ (v1_relat_1 @ X42))),
% 0.89/1.16      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.89/1.16  thf('162', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         ((r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.89/1.16           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['160', '161'])).
% 0.89/1.16  thf('163', plain, (![X49 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X49)) = (X49))),
% 0.89/1.16      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.16  thf('164', plain, (![X49 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X49)) = (X49))),
% 0.89/1.16      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.16  thf('165', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('166', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.16  thf('167', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.89/1.16      inference('demod', [status(thm)], ['162', '163', '164', '165', '166'])).
% 0.89/1.16  thf('168', plain,
% 0.89/1.16      (![X51 : $i, X52 : $i]:
% 0.89/1.16         (~ (r1_tarski @ (k1_relat_1 @ X51) @ X52)
% 0.89/1.16          | ((k5_relat_1 @ (k6_relat_1 @ X52) @ X51) = (X51))
% 0.89/1.16          | ~ (v1_relat_1 @ X51))),
% 0.89/1.16      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.89/1.16  thf('169', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X0)
% 0.89/1.16          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['167', '168'])).
% 0.89/1.16  thf('170', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.16            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.89/1.16          | ~ (v1_relat_1 @ X1))),
% 0.89/1.16      inference('demod', [status(thm)], ['109', '110'])).
% 0.89/1.16  thf('171', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (((k4_relat_1 @ X0)
% 0.89/1.16            = (k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 0.89/1.16               (k6_relat_1 @ (k1_relat_1 @ X0))))
% 0.89/1.16          | ~ (v1_relat_1 @ X0)
% 0.89/1.16          | ~ (v1_relat_1 @ X0))),
% 0.89/1.16      inference('sup+', [status(thm)], ['169', '170'])).
% 0.89/1.16  thf('172', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X0)
% 0.89/1.16          | ((k4_relat_1 @ X0)
% 0.89/1.16              = (k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 0.89/1.16                 (k6_relat_1 @ (k1_relat_1 @ X0)))))),
% 0.89/1.16      inference('simplify', [status(thm)], ['171'])).
% 0.89/1.16  thf('173', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.89/1.16               (k6_relat_1 @ 
% 0.89/1.16                (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))))
% 0.89/1.16          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['159', '172'])).
% 0.89/1.16  thf('174', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('sup+', [status(thm)], ['157', '158'])).
% 0.89/1.16  thf('175', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.16           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.89/1.16      inference('demod', [status(thm)], ['42', '43'])).
% 0.89/1.16  thf('176', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k4_relat_1 @ 
% 0.89/1.16           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.89/1.16           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ 
% 0.89/1.16              (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['126', '127'])).
% 0.89/1.16  thf('177', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k4_relat_1 @ 
% 0.89/1.16           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2))
% 0.89/1.16           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.89/1.16  thf('178', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 0.89/1.16           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ 
% 0.89/1.16              (k6_relat_1 @ X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['176', '177'])).
% 0.89/1.16  thf('179', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.89/1.16  thf('180', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.89/1.16              (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.89/1.16      inference('demod', [status(thm)], ['152', '153'])).
% 0.89/1.16  thf('181', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.89/1.16  thf('182', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.16  thf('183', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.16              (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.89/1.16      inference('demod', [status(thm)],
% 0.89/1.16                ['173', '174', '175', '178', '179', '180', '181', '182'])).
% 0.89/1.16  thf('184', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.89/1.16           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['155', '156', '183'])).
% 0.89/1.16  thf('185', plain,
% 0.89/1.16      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.89/1.16         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.89/1.16      inference('demod', [status(thm)], ['6', '184'])).
% 0.89/1.16  thf('186', plain, ($false), inference('simplify', [status(thm)], ['185'])).
% 0.89/1.16  
% 0.89/1.16  % SZS output end Refutation
% 0.89/1.16  
% 0.89/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
