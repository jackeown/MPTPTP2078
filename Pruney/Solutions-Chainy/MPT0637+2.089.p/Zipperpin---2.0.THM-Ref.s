%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LGtYx2tk4y

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:09 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  181 (3294 expanded)
%              Number of leaves         :   30 (1197 expanded)
%              Depth                    :   25
%              Number of atoms          : 1564 (27735 expanded)
%              Number of equality atoms :  108 (1862 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ ( k1_relat_1 @ X35 ) )
        = X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('12',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('19',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('30',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('32',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('37',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k8_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k5_relat_1 @ X17 @ ( k8_relat_1 @ X18 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k8_relat_1 @ X15 @ X14 )
        = ( k3_xboole_0 @ X14 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k8_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k5_relat_1 @ X17 @ ( k8_relat_1 @ X18 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('49',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('50',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('53',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('60',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k8_relat_1 @ X15 @ X14 )
        = ( k3_xboole_0 @ X14 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['61','70'])).

thf('72',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('76',plain,(
    ! [X28: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X28 ) )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('77',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X21 ) @ ( k4_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('88',plain,(
    ! [X28: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X28 ) )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('89',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k8_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k5_relat_1 @ X17 @ ( k8_relat_1 @ X18 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('90',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('92',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('98',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('101',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['90','102'])).

thf('104',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('105',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k8_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('109',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('110',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('113',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','111','112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','111','112','113'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['83','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('119',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('125',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['117','118','123','124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('128',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) @ X11 )
        = ( k7_relat_1 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('131',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ) ),
    inference('sup+',[status(thm)],['126','132'])).

thf('134',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('135',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['47','133','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','136'])).

thf('138',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['117','118','123','124','125'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['47','133','134','135'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['117','118','123','124','125'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['117','118','123','124','125'])).

thf('148',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','146','147'])).

thf('149',plain,(
    $false ),
    inference(simplify,[status(thm)],['148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LGtYx2tk4y
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:09 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 750 iterations in 0.444s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.71/0.90  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.71/0.90  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.71/0.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.71/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.90  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.71/0.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.71/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(t123_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.71/0.90  thf('0', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X13 @ X12) = (k5_relat_1 @ X12 @ (k6_relat_1 @ X13)))
% 0.71/0.90          | ~ (v1_relat_1 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.71/0.90  thf(t43_funct_1, conjecture,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.71/0.90       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.71/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.90    (~( ![A:$i,B:$i]:
% 0.71/0.90        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.71/0.90          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.71/0.90         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('2', plain,
% 0.71/0.90      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.71/0.90          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.71/0.90        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['0', '1'])).
% 0.71/0.90  thf(fc3_funct_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.71/0.90       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.71/0.90  thf('3', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('4', plain,
% 0.71/0.90      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.71/0.90         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.71/0.90      inference('demod', [status(thm)], ['2', '3'])).
% 0.71/0.90  thf('5', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X13 @ X12) = (k5_relat_1 @ X12 @ (k6_relat_1 @ X13)))
% 0.71/0.90          | ~ (v1_relat_1 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.71/0.90  thf(t71_relat_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.71/0.90       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.71/0.90  thf('6', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.71/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.71/0.90  thf(t98_relat_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ A ) =>
% 0.71/0.90       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.71/0.90  thf('7', plain,
% 0.71/0.90      (![X35 : $i]:
% 0.71/0.90         (((k7_relat_1 @ X35 @ (k1_relat_1 @ X35)) = (X35))
% 0.71/0.90          | ~ (v1_relat_1 @ X35))),
% 0.71/0.90      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['6', '7'])).
% 0.71/0.90  thf('9', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('10', plain,
% 0.71/0.90      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['8', '9'])).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X13 @ X12) = (k5_relat_1 @ X12 @ (k6_relat_1 @ X13)))
% 0.71/0.90          | ~ (v1_relat_1 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.71/0.90  thf(t94_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      (![X33 : $i, X34 : $i]:
% 0.71/0.90         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 0.71/0.90          | ~ (v1_relat_1 @ X34))),
% 0.71/0.90      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.71/0.90  thf('13', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.71/0.90            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['11', '12'])).
% 0.71/0.90  thf('14', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('15', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('16', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.71/0.90  thf('17', plain,
% 0.71/0.90      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['10', '16'])).
% 0.71/0.90  thf('18', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X13 @ X12) = (k5_relat_1 @ X12 @ (k6_relat_1 @ X13)))
% 0.71/0.90          | ~ (v1_relat_1 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.71/0.90  thf(t76_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.71/0.90         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.71/0.90  thf('19', plain,
% 0.71/0.90      (![X29 : $i, X30 : $i]:
% 0.71/0.90         ((r1_tarski @ (k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) @ X29)
% 0.71/0.90          | ~ (v1_relat_1 @ X29))),
% 0.71/0.90      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.71/0.90  thf('20', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.71/0.90          | ~ (v1_relat_1 @ X0)
% 0.71/0.90          | ~ (v1_relat_1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['18', '19'])).
% 0.71/0.90  thf('21', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 0.71/0.90      inference('simplify', [status(thm)], ['20'])).
% 0.71/0.90  thf('22', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r1_tarski @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['17', '21'])).
% 0.71/0.90  thf('23', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('24', plain,
% 0.71/0.90      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['22', '23'])).
% 0.71/0.90  thf(t25_relat_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ A ) =>
% 0.71/0.90       ( ![B:$i]:
% 0.71/0.90         ( ( v1_relat_1 @ B ) =>
% 0.71/0.90           ( ( r1_tarski @ A @ B ) =>
% 0.71/0.90             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.71/0.90               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.71/0.90  thf('25', plain,
% 0.71/0.90      (![X19 : $i, X20 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X19)
% 0.71/0.90          | (r1_tarski @ (k2_relat_1 @ X20) @ (k2_relat_1 @ X19))
% 0.71/0.90          | ~ (r1_tarski @ X20 @ X19)
% 0.71/0.90          | ~ (v1_relat_1 @ X20))),
% 0.71/0.90      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.71/0.90  thf('26', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.71/0.90          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.71/0.90             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['24', '25'])).
% 0.71/0.90  thf('27', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('28', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.71/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.71/0.90  thf('29', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.71/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.71/0.90  thf('30', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('31', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.71/0.90      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.71/0.90  thf(t79_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.71/0.90         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.71/0.90  thf('32', plain,
% 0.71/0.90      (![X31 : $i, X32 : $i]:
% 0.71/0.90         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 0.71/0.90          | ((k5_relat_1 @ X31 @ (k6_relat_1 @ X32)) = (X31))
% 0.71/0.90          | ~ (v1_relat_1 @ X31))),
% 0.71/0.90      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.71/0.90  thf('33', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X0)
% 0.71/0.90          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['31', '32'])).
% 0.71/0.90  thf('34', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0))
% 0.71/0.90          | ~ (v1_relat_1 @ X0)
% 0.71/0.90          | ~ (v1_relat_1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['5', '33'])).
% 0.71/0.90  thf('35', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['34'])).
% 0.71/0.90  thf('36', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X13 @ X12) = (k5_relat_1 @ X12 @ (k6_relat_1 @ X13)))
% 0.71/0.90          | ~ (v1_relat_1 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.71/0.90  thf('37', plain,
% 0.71/0.90      (![X33 : $i, X34 : $i]:
% 0.71/0.90         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 0.71/0.90          | ~ (v1_relat_1 @ X34))),
% 0.71/0.90      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.71/0.90  thf(t139_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( ![C:$i]:
% 0.71/0.90         ( ( v1_relat_1 @ C ) =>
% 0.71/0.90           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.71/0.90             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.71/0.90  thf('38', plain,
% 0.71/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X16)
% 0.71/0.90          | ((k8_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X16))
% 0.71/0.90              = (k5_relat_1 @ X17 @ (k8_relat_1 @ X18 @ X16)))
% 0.71/0.90          | ~ (v1_relat_1 @ X17))),
% 0.71/0.90      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.71/0.90  thf('39', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.71/0.90            = (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ (k8_relat_1 @ X2 @ X1))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['37', '38'])).
% 0.71/0.90  thf('40', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('41', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.71/0.90            = (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ (k8_relat_1 @ X2 @ X1))
% 0.71/0.90          | ~ (v1_relat_1 @ X1))),
% 0.71/0.90      inference('demod', [status(thm)], ['39', '40'])).
% 0.71/0.90  thf(t124_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( ( k8_relat_1 @ A @ B ) =
% 0.71/0.90         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.71/0.90  thf('42', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X15 @ X14)
% 0.71/0.90            = (k3_xboole_0 @ X14 @ (k2_zfmisc_1 @ (k1_relat_1 @ X14) @ X15)))
% 0.71/0.90          | ~ (v1_relat_1 @ X14))),
% 0.71/0.90      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.71/0.90  thf(fc1_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.71/0.90  thf('43', plain,
% 0.71/0.90      (![X7 : $i, X8 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.71/0.90  thf('44', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ X0)
% 0.71/0.90          | ~ (v1_relat_1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['42', '43'])).
% 0.71/0.90  thf('45', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['44'])).
% 0.71/0.90  thf('46', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X1)
% 0.71/0.90          | ((k8_relat_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.71/0.90              = (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)))),
% 0.71/0.90      inference('clc', [status(thm)], ['41', '45'])).
% 0.71/0.90  thf('47', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90            = (k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['36', '46'])).
% 0.71/0.90  thf('48', plain,
% 0.71/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X16)
% 0.71/0.90          | ((k8_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X16))
% 0.71/0.90              = (k5_relat_1 @ X17 @ (k8_relat_1 @ X18 @ X16)))
% 0.71/0.90          | ~ (v1_relat_1 @ X17))),
% 0.71/0.90      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.71/0.90  thf('49', plain,
% 0.71/0.90      (![X33 : $i, X34 : $i]:
% 0.71/0.90         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 0.71/0.90          | ~ (v1_relat_1 @ X34))),
% 0.71/0.90      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.71/0.90  thf('50', plain,
% 0.71/0.90      (![X29 : $i, X30 : $i]:
% 0.71/0.90         ((r1_tarski @ (k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) @ X29)
% 0.71/0.90          | ~ (v1_relat_1 @ X29))),
% 0.71/0.90      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.71/0.90  thf('51', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.71/0.90           (k6_relat_1 @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['49', '50'])).
% 0.71/0.90  thf('52', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('53', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('54', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.71/0.90  thf('55', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.71/0.90  thf('56', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['54', '55'])).
% 0.71/0.90  thf('57', plain,
% 0.71/0.90      (![X19 : $i, X20 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X19)
% 0.71/0.90          | (r1_tarski @ (k2_relat_1 @ X20) @ (k2_relat_1 @ X19))
% 0.71/0.90          | ~ (r1_tarski @ X20 @ X19)
% 0.71/0.90          | ~ (v1_relat_1 @ X20))),
% 0.71/0.90      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.71/0.90  thf('58', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90          | (r1_tarski @ 
% 0.71/0.90             (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.71/0.90             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['56', '57'])).
% 0.71/0.90  thf('59', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.71/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.71/0.90  thf('60', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('61', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90          | (r1_tarski @ 
% 0.71/0.90             (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.71/0.90  thf('62', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.71/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.71/0.90  thf('63', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X15 @ X14)
% 0.71/0.90            = (k3_xboole_0 @ X14 @ (k2_zfmisc_1 @ (k1_relat_1 @ X14) @ X15)))
% 0.71/0.90          | ~ (v1_relat_1 @ X14))),
% 0.71/0.90      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.71/0.90  thf('64', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.71/0.90            = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['62', '63'])).
% 0.71/0.90  thf('65', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('66', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.71/0.90           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['64', '65'])).
% 0.71/0.90  thf('67', plain,
% 0.71/0.90      (![X7 : $i, X8 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.71/0.90  thf('68', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['66', '67'])).
% 0.71/0.90  thf('69', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('70', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['68', '69'])).
% 0.71/0.90  thf('71', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)),
% 0.71/0.90      inference('demod', [status(thm)], ['61', '70'])).
% 0.71/0.90  thf('72', plain,
% 0.71/0.90      (![X31 : $i, X32 : $i]:
% 0.71/0.90         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 0.71/0.90          | ((k5_relat_1 @ X31 @ (k6_relat_1 @ X32)) = (X31))
% 0.71/0.90          | ~ (v1_relat_1 @ X31))),
% 0.71/0.90      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.71/0.90  thf('73', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90          | ((k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.71/0.90              (k6_relat_1 @ X0)) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['71', '72'])).
% 0.71/0.90  thf('74', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['68', '69'])).
% 0.71/0.90  thf('75', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.71/0.90           (k6_relat_1 @ X0)) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['73', '74'])).
% 0.71/0.90  thf(t72_relat_1, axiom,
% 0.71/0.90    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.71/0.90  thf('76', plain,
% 0.71/0.90      (![X28 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X28)) = (k6_relat_1 @ X28))),
% 0.71/0.90      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.71/0.90  thf(t54_relat_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ A ) =>
% 0.71/0.90       ( ![B:$i]:
% 0.71/0.90         ( ( v1_relat_1 @ B ) =>
% 0.71/0.90           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.71/0.90             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.71/0.90  thf('77', plain,
% 0.71/0.90      (![X21 : $i, X22 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X21)
% 0.71/0.90          | ((k4_relat_1 @ (k5_relat_1 @ X22 @ X21))
% 0.71/0.90              = (k5_relat_1 @ (k4_relat_1 @ X21) @ (k4_relat_1 @ X22)))
% 0.71/0.90          | ~ (v1_relat_1 @ X22))),
% 0.71/0.90      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.71/0.90  thf('78', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.71/0.90          | ~ (v1_relat_1 @ X1)
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['76', '77'])).
% 0.71/0.90  thf('79', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('80', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.71/0.90          | ~ (v1_relat_1 @ X1))),
% 0.71/0.90      inference('demod', [status(thm)], ['78', '79'])).
% 0.71/0.90  thf('81', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.71/0.90               (k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))
% 0.71/0.90          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.71/0.90      inference('sup+', [status(thm)], ['75', '80'])).
% 0.71/0.90  thf('82', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['68', '69'])).
% 0.71/0.90  thf('83', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.71/0.90              (k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 0.71/0.90      inference('demod', [status(thm)], ['81', '82'])).
% 0.71/0.90  thf('84', plain,
% 0.71/0.90      (![X33 : $i, X34 : $i]:
% 0.71/0.90         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 0.71/0.90          | ~ (v1_relat_1 @ X34))),
% 0.71/0.90      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.71/0.90  thf('85', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.71/0.90          | ~ (v1_relat_1 @ X1))),
% 0.71/0.90      inference('demod', [status(thm)], ['78', '79'])).
% 0.71/0.90  thf('86', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.71/0.90            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.71/0.90               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['84', '85'])).
% 0.71/0.90  thf('87', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.71/0.90  thf('88', plain,
% 0.71/0.90      (![X28 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X28)) = (k6_relat_1 @ X28))),
% 0.71/0.90      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.71/0.90  thf('89', plain,
% 0.71/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X16)
% 0.71/0.90          | ((k8_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X16))
% 0.71/0.90              = (k5_relat_1 @ X17 @ (k8_relat_1 @ X18 @ X16)))
% 0.71/0.90          | ~ (v1_relat_1 @ X17))),
% 0.71/0.90      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.71/0.90  thf('90', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X13 @ X12) = (k5_relat_1 @ X12 @ (k6_relat_1 @ X13)))
% 0.71/0.90          | ~ (v1_relat_1 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.71/0.90  thf('91', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.71/0.90      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.71/0.90  thf('92', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.71/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.71/0.90  thf('93', plain,
% 0.71/0.90      (![X31 : $i, X32 : $i]:
% 0.71/0.90         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 0.71/0.90          | ((k5_relat_1 @ X31 @ (k6_relat_1 @ X32)) = (X31))
% 0.71/0.90          | ~ (v1_relat_1 @ X31))),
% 0.71/0.90      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.71/0.90  thf('94', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (r1_tarski @ X0 @ X1)
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.71/0.90          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.71/0.90              = (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['92', '93'])).
% 0.71/0.90  thf('95', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('96', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (r1_tarski @ X0 @ X1)
% 0.71/0.90          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.71/0.90              = (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['94', '95'])).
% 0.71/0.90  thf('97', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.71/0.90           = (k6_relat_1 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['91', '96'])).
% 0.71/0.90  thf(t55_relat_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ A ) =>
% 0.71/0.90       ( ![B:$i]:
% 0.71/0.90         ( ( v1_relat_1 @ B ) =>
% 0.71/0.90           ( ![C:$i]:
% 0.71/0.90             ( ( v1_relat_1 @ C ) =>
% 0.71/0.90               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.71/0.90                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.71/0.90  thf('98', plain,
% 0.71/0.90      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X23)
% 0.71/0.90          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 0.71/0.90              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 0.71/0.90          | ~ (v1_relat_1 @ X25)
% 0.71/0.90          | ~ (v1_relat_1 @ X24))),
% 0.71/0.90      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.71/0.90  thf('99', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.71/0.90            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.71/0.90               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ X1)
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['97', '98'])).
% 0.71/0.90  thf('100', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('101', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('102', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.71/0.90            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.71/0.90               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.71/0.90          | ~ (v1_relat_1 @ X1))),
% 0.71/0.90      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.71/0.90  thf('103', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.71/0.90            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.71/0.90               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['90', '102'])).
% 0.71/0.90  thf('104', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('105', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('106', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.71/0.90           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.71/0.90              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.71/0.90      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.71/0.90  thf('107', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.71/0.90            = (k8_relat_1 @ X1 @ 
% 0.71/0.90               (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['89', '106'])).
% 0.71/0.90  thf('108', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.71/0.90           = (k6_relat_1 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['91', '96'])).
% 0.71/0.90  thf('109', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('110', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('111', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.71/0.90  thf('112', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('113', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('114', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['86', '87', '88', '111', '112', '113'])).
% 0.71/0.90  thf('115', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['86', '87', '88', '111', '112', '113'])).
% 0.71/0.90  thf('116', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.71/0.90           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.71/0.90              (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.71/0.90      inference('demod', [status(thm)], ['83', '114', '115'])).
% 0.71/0.90  thf('117', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.71/0.90            = (k8_relat_1 @ X1 @ 
% 0.71/0.90               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['48', '116'])).
% 0.71/0.90  thf('118', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.71/0.90  thf('119', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X13 @ X12) = (k5_relat_1 @ X12 @ (k6_relat_1 @ X13)))
% 0.71/0.90          | ~ (v1_relat_1 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.71/0.90  thf('120', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.71/0.90           (k6_relat_1 @ X0)) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['73', '74'])).
% 0.71/0.90  thf('121', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.71/0.90      inference('sup+', [status(thm)], ['119', '120'])).
% 0.71/0.90  thf('122', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['68', '69'])).
% 0.71/0.90  thf('123', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['121', '122'])).
% 0.71/0.90  thf('124', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('125', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('126', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.71/0.90           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['117', '118', '123', '124', '125'])).
% 0.71/0.90  thf('127', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.71/0.90  thf(t100_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ C ) =>
% 0.71/0.90       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.71/0.90         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.71/0.90  thf('128', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.90         (((k7_relat_1 @ (k7_relat_1 @ X9 @ X10) @ X11)
% 0.71/0.90            = (k7_relat_1 @ X9 @ (k3_xboole_0 @ X10 @ X11)))
% 0.71/0.90          | ~ (v1_relat_1 @ X9))),
% 0.71/0.90      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.71/0.90  thf('129', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.71/0.90            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['127', '128'])).
% 0.71/0.90  thf('130', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.71/0.90  thf('131', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('132', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.71/0.90      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.71/0.90  thf('133', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.71/0.90           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X2))))),
% 0.71/0.90      inference('sup+', [status(thm)], ['126', '132'])).
% 0.71/0.90  thf('134', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('135', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('136', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X2 @ X0))))),
% 0.71/0.90      inference('demod', [status(thm)], ['47', '133', '134', '135'])).
% 0.71/0.90  thf('137', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k8_relat_1 @ X1 @ 
% 0.71/0.90            (k8_relat_1 @ 
% 0.71/0.90             (k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.71/0.90             (k6_relat_1 @ X0)))
% 0.71/0.90            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.71/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.71/0.90      inference('sup+', [status(thm)], ['35', '136'])).
% 0.71/0.90  thf('138', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.71/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.71/0.90  thf('139', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.71/0.90           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['117', '118', '123', '124', '125'])).
% 0.71/0.90  thf('140', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X2 @ X0))))),
% 0.71/0.90      inference('demod', [status(thm)], ['47', '133', '134', '135'])).
% 0.71/0.90  thf('141', plain,
% 0.71/0.90      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['10', '16'])).
% 0.71/0.90  thf('142', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.71/0.90           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['117', '118', '123', '124', '125'])).
% 0.71/0.90  thf('143', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['121', '122'])).
% 0.71/0.90  thf('144', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.71/0.90           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['142', '143'])).
% 0.71/0.90  thf('145', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.71/0.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.71/0.90  thf('146', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.71/0.90           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)],
% 0.71/0.90                ['137', '138', '139', '140', '141', '144', '145'])).
% 0.71/0.90  thf('147', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.71/0.90           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['117', '118', '123', '124', '125'])).
% 0.71/0.90  thf('148', plain,
% 0.71/0.90      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.71/0.90         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.71/0.90      inference('demod', [status(thm)], ['4', '146', '147'])).
% 0.71/0.90  thf('149', plain, ($false), inference('simplify', [status(thm)], ['148'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
