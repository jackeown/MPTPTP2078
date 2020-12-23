%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tIXSA49kRz

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:04 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 779 expanded)
%              Number of leaves         :   29 ( 288 expanded)
%              Depth                    :   18
%              Number of atoms          : 1236 (6097 expanded)
%              Number of equality atoms :   89 ( 437 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
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
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('5',plain,(
    ! [X51: $i] :
      ( ( ( k5_relat_1 @ X51 @ ( k6_relat_1 @ ( k2_relat_1 @ X51 ) ) )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ X56 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X33 @ X32 ) @ X34 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('13',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ X56 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X40 @ X41 ) )
        = ( k9_relat_1 @ X40 @ X41 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('27',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('28',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('30',plain,(
    ! [X47: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X46: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('38',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X58 ) @ X59 )
      | ( ( k7_relat_1 @ X58 @ X59 )
        = X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('46',plain,(
    ! [X46: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) ) @ ( k1_relat_1 @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('53',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X49 ) @ X50 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X50 ) @ X49 )
        = X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('56',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ X56 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['54','64'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('66',plain,(
    ! [X48: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X48 ) )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X45 @ X44 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X44 ) @ ( k4_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('73',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ X56 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('74',plain,(
    ! [X48: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X48 ) )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('75',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X45 @ X44 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X44 ) @ ( k4_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('81',plain,(
    ! [X48: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X48 ) )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('82',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('83',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','84'])).

thf('86',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','87','88','89'])).

thf('91',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('94',plain,(
    ! [X47: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('96',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('102',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','24','25','44','45','99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','24','25','44','45','99','100','101','102'])).

thf('105',plain,(
    ! [X46: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('108',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X54 @ X55 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X46: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('111',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['103','113'])).

thf('115',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','114'])).

thf('116',plain,(
    $false ),
    inference(simplify,[status(thm)],['115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tIXSA49kRz
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.80  % Solved by: fo/fo7.sh
% 0.61/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.80  % done 494 iterations in 0.342s
% 0.61/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.80  % SZS output start Refutation
% 0.61/0.80  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.61/0.80  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.61/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.61/0.80  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.61/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.80  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.61/0.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.61/0.80  thf(t123_relat_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ B ) =>
% 0.61/0.80       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.61/0.80  thf('0', plain,
% 0.61/0.80      (![X35 : $i, X36 : $i]:
% 0.61/0.80         (((k8_relat_1 @ X36 @ X35) = (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)))
% 0.61/0.80          | ~ (v1_relat_1 @ X35))),
% 0.61/0.80      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.61/0.80  thf(t43_funct_1, conjecture,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.61/0.80       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.80    (~( ![A:$i,B:$i]:
% 0.61/0.80        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.61/0.80          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.61/0.80    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.61/0.80  thf('1', plain,
% 0.61/0.80      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.61/0.80         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('2', plain,
% 0.61/0.80      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.61/0.80          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.61/0.80        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.61/0.80  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.61/0.80  thf('3', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('4', plain,
% 0.61/0.80      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.61/0.80         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.61/0.80      inference('demod', [status(thm)], ['2', '3'])).
% 0.61/0.80  thf(t80_relat_1, axiom,
% 0.61/0.80    (![A:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ A ) =>
% 0.61/0.80       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.61/0.80  thf('5', plain,
% 0.61/0.80      (![X51 : $i]:
% 0.61/0.80         (((k5_relat_1 @ X51 @ (k6_relat_1 @ (k2_relat_1 @ X51))) = (X51))
% 0.61/0.80          | ~ (v1_relat_1 @ X51))),
% 0.61/0.80      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.61/0.80  thf(t94_relat_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ B ) =>
% 0.61/0.80       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.61/0.80  thf('6', plain,
% 0.61/0.80      (![X56 : $i, X57 : $i]:
% 0.61/0.80         (((k7_relat_1 @ X57 @ X56) = (k5_relat_1 @ (k6_relat_1 @ X56) @ X57))
% 0.61/0.80          | ~ (v1_relat_1 @ X57))),
% 0.61/0.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.61/0.80  thf(t112_relat_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ B ) =>
% 0.61/0.80       ( ![C:$i]:
% 0.61/0.80         ( ( v1_relat_1 @ C ) =>
% 0.61/0.80           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.61/0.80             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.61/0.80  thf('7', plain,
% 0.61/0.80      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X32)
% 0.61/0.80          | ((k7_relat_1 @ (k5_relat_1 @ X33 @ X32) @ X34)
% 0.61/0.80              = (k5_relat_1 @ (k7_relat_1 @ X33 @ X34) @ X32))
% 0.61/0.80          | ~ (v1_relat_1 @ X33))),
% 0.61/0.80      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.61/0.80  thf('8', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.80         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.61/0.80            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 0.61/0.80          | ~ (v1_relat_1 @ X1)
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.61/0.80          | ~ (v1_relat_1 @ X1))),
% 0.61/0.80      inference('sup+', [status(thm)], ['6', '7'])).
% 0.61/0.80  thf('9', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('10', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.80         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.61/0.80            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 0.61/0.80          | ~ (v1_relat_1 @ X1)
% 0.61/0.80          | ~ (v1_relat_1 @ X1))),
% 0.61/0.80      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.80  thf('11', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X1)
% 0.61/0.80          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.61/0.80              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)))),
% 0.61/0.80      inference('simplify', [status(thm)], ['10'])).
% 0.61/0.80  thf('12', plain,
% 0.61/0.80      (![X35 : $i, X36 : $i]:
% 0.61/0.80         (((k8_relat_1 @ X36 @ X35) = (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)))
% 0.61/0.80          | ~ (v1_relat_1 @ X35))),
% 0.61/0.80      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.61/0.80  thf('13', plain,
% 0.61/0.80      (![X56 : $i, X57 : $i]:
% 0.61/0.80         (((k7_relat_1 @ X57 @ X56) = (k5_relat_1 @ (k6_relat_1 @ X56) @ X57))
% 0.61/0.80          | ~ (v1_relat_1 @ X57))),
% 0.61/0.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.61/0.80  thf('14', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['12', '13'])).
% 0.61/0.80  thf('15', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('16', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('17', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.61/0.80  thf('18', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X1)
% 0.61/0.80          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.61/0.80              = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)) @ X1)))),
% 0.61/0.80      inference('demod', [status(thm)], ['11', '17'])).
% 0.61/0.80  thf('19', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k7_relat_1 @ 
% 0.61/0.80            (k7_relat_1 @ 
% 0.61/0.80             (k6_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.61/0.80             X1) @ 
% 0.61/0.80            X0) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80          | ~ (v1_relat_1 @ 
% 0.61/0.80               (k6_relat_1 @ 
% 0.61/0.80                (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))))),
% 0.61/0.80      inference('sup+', [status(thm)], ['5', '18'])).
% 0.61/0.80  thf('20', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.61/0.80  thf(t148_relat_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ B ) =>
% 0.61/0.80       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.61/0.80  thf('21', plain,
% 0.61/0.80      (![X40 : $i, X41 : $i]:
% 0.61/0.80         (((k2_relat_1 @ (k7_relat_1 @ X40 @ X41)) = (k9_relat_1 @ X40 @ X41))
% 0.61/0.80          | ~ (v1_relat_1 @ X40))),
% 0.61/0.80      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.61/0.80  thf('22', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['20', '21'])).
% 0.61/0.80  thf('23', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('24', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['22', '23'])).
% 0.61/0.80  thf('25', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.61/0.80  thf('26', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['22', '23'])).
% 0.61/0.80  thf('27', plain,
% 0.61/0.80      (![X35 : $i, X36 : $i]:
% 0.61/0.80         (((k8_relat_1 @ X36 @ X35) = (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)))
% 0.61/0.80          | ~ (v1_relat_1 @ X35))),
% 0.61/0.80      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.61/0.80  thf(t45_relat_1, axiom,
% 0.61/0.80    (![A:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ A ) =>
% 0.61/0.80       ( ![B:$i]:
% 0.61/0.80         ( ( v1_relat_1 @ B ) =>
% 0.61/0.80           ( r1_tarski @
% 0.61/0.80             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.61/0.80  thf('28', plain,
% 0.61/0.80      (![X42 : $i, X43 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X42)
% 0.61/0.80          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X43 @ X42)) @ 
% 0.61/0.80             (k2_relat_1 @ X42))
% 0.61/0.80          | ~ (v1_relat_1 @ X43))),
% 0.61/0.80      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.61/0.80  thf('29', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.61/0.80           (k2_relat_1 @ (k6_relat_1 @ X1)))
% 0.61/0.80          | ~ (v1_relat_1 @ X0)
% 0.61/0.80          | ~ (v1_relat_1 @ X0)
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['27', '28'])).
% 0.61/0.80  thf(t71_relat_1, axiom,
% 0.61/0.80    (![A:$i]:
% 0.61/0.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.61/0.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.61/0.80  thf('30', plain, (![X47 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 0.61/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.80  thf('31', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('32', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 0.61/0.80          | ~ (v1_relat_1 @ X0)
% 0.61/0.80          | ~ (v1_relat_1 @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.61/0.80  thf('33', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X0)
% 0.61/0.80          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X1))),
% 0.61/0.80      inference('simplify', [status(thm)], ['32'])).
% 0.61/0.80  thf('34', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['26', '33'])).
% 0.61/0.80  thf('35', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('36', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)),
% 0.61/0.80      inference('demod', [status(thm)], ['34', '35'])).
% 0.61/0.80  thf('37', plain, (![X46 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.61/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.80  thf(t97_relat_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ B ) =>
% 0.61/0.80       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.61/0.80         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.61/0.80  thf('38', plain,
% 0.61/0.80      (![X58 : $i, X59 : $i]:
% 0.61/0.80         (~ (r1_tarski @ (k1_relat_1 @ X58) @ X59)
% 0.61/0.80          | ((k7_relat_1 @ X58 @ X59) = (X58))
% 0.61/0.80          | ~ (v1_relat_1 @ X58))),
% 0.61/0.80      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.61/0.80  thf('39', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (r1_tarski @ X0 @ X1)
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.61/0.80          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.61/0.80  thf('40', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('41', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (r1_tarski @ X0 @ X1)
% 0.61/0.80          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['39', '40'])).
% 0.61/0.80  thf('42', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.61/0.80  thf('43', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (r1_tarski @ X0 @ X1)
% 0.61/0.80          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['41', '42'])).
% 0.61/0.80  thf('44', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k8_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.61/0.80           (k6_relat_1 @ X0))
% 0.61/0.80           = (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['36', '43'])).
% 0.61/0.80  thf('45', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.61/0.80  thf('46', plain, (![X46 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.61/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.80  thf(t89_relat_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ B ) =>
% 0.61/0.80       ( r1_tarski @
% 0.61/0.80         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.61/0.80  thf('47', plain,
% 0.61/0.80      (![X52 : $i, X53 : $i]:
% 0.61/0.80         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X52 @ X53)) @ 
% 0.61/0.80           (k1_relat_1 @ X52))
% 0.61/0.80          | ~ (v1_relat_1 @ X52))),
% 0.61/0.80      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.61/0.80  thf('48', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.61/0.80           X0)
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['46', '47'])).
% 0.61/0.80  thf('49', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('50', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X0)),
% 0.61/0.80      inference('demod', [status(thm)], ['48', '49'])).
% 0.61/0.80  thf('51', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.61/0.80  thf('52', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ X0)),
% 0.61/0.80      inference('demod', [status(thm)], ['50', '51'])).
% 0.61/0.80  thf(t77_relat_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ B ) =>
% 0.61/0.80       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.61/0.80         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.61/0.80  thf('53', plain,
% 0.61/0.80      (![X49 : $i, X50 : $i]:
% 0.61/0.80         (~ (r1_tarski @ (k1_relat_1 @ X49) @ X50)
% 0.61/0.80          | ((k5_relat_1 @ (k6_relat_1 @ X50) @ X49) = (X49))
% 0.61/0.80          | ~ (v1_relat_1 @ X49))),
% 0.61/0.80      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.61/0.80  thf('54', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.61/0.80          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.61/0.80              (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.61/0.80              = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.61/0.80      inference('sup-', [status(thm)], ['52', '53'])).
% 0.61/0.80  thf('55', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.61/0.80  thf('56', plain,
% 0.61/0.80      (![X56 : $i, X57 : $i]:
% 0.61/0.80         (((k7_relat_1 @ X57 @ X56) = (k5_relat_1 @ (k6_relat_1 @ X56) @ X57))
% 0.61/0.80          | ~ (v1_relat_1 @ X57))),
% 0.61/0.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.61/0.80  thf(dt_k5_relat_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.61/0.80       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.61/0.80  thf('57', plain,
% 0.61/0.80      (![X29 : $i, X30 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X29)
% 0.61/0.80          | ~ (v1_relat_1 @ X30)
% 0.61/0.80          | (v1_relat_1 @ (k5_relat_1 @ X29 @ X30)))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.61/0.80  thf('58', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.61/0.80          | ~ (v1_relat_1 @ X1)
% 0.61/0.80          | ~ (v1_relat_1 @ X1)
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['56', '57'])).
% 0.61/0.80  thf('59', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('60', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.61/0.80          | ~ (v1_relat_1 @ X1)
% 0.61/0.80          | ~ (v1_relat_1 @ X1))),
% 0.61/0.80      inference('demod', [status(thm)], ['58', '59'])).
% 0.61/0.80  thf('61', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.61/0.80      inference('simplify', [status(thm)], ['60'])).
% 0.61/0.80  thf('62', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['55', '61'])).
% 0.61/0.80  thf('63', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('64', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.80  thf('65', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.61/0.80           (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.61/0.80           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.61/0.80      inference('demod', [status(thm)], ['54', '64'])).
% 0.61/0.80  thf(t72_relat_1, axiom,
% 0.61/0.80    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.61/0.80  thf('66', plain,
% 0.61/0.80      (![X48 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X48)) = (k6_relat_1 @ X48))),
% 0.61/0.80      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.61/0.80  thf(t54_relat_1, axiom,
% 0.61/0.80    (![A:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ A ) =>
% 0.61/0.80       ( ![B:$i]:
% 0.61/0.80         ( ( v1_relat_1 @ B ) =>
% 0.61/0.80           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.61/0.80             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.61/0.80  thf('67', plain,
% 0.61/0.80      (![X44 : $i, X45 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X44)
% 0.61/0.80          | ((k4_relat_1 @ (k5_relat_1 @ X45 @ X44))
% 0.61/0.80              = (k5_relat_1 @ (k4_relat_1 @ X44) @ (k4_relat_1 @ X45)))
% 0.61/0.80          | ~ (v1_relat_1 @ X45))),
% 0.61/0.80      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.61/0.80  thf('68', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.61/0.80            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.61/0.80          | ~ (v1_relat_1 @ X1))),
% 0.61/0.80      inference('sup+', [status(thm)], ['66', '67'])).
% 0.61/0.80  thf('69', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('70', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.61/0.80            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.61/0.80          | ~ (v1_relat_1 @ X1))),
% 0.61/0.80      inference('demod', [status(thm)], ['68', '69'])).
% 0.61/0.80  thf('71', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80            = (k5_relat_1 @ 
% 0.61/0.80               (k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.61/0.80               (k6_relat_1 @ X1)))
% 0.61/0.80          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.61/0.80      inference('sup+', [status(thm)], ['65', '70'])).
% 0.61/0.80  thf('72', plain,
% 0.61/0.80      (![X35 : $i, X36 : $i]:
% 0.61/0.80         (((k8_relat_1 @ X36 @ X35) = (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)))
% 0.61/0.80          | ~ (v1_relat_1 @ X35))),
% 0.61/0.80      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.61/0.80  thf('73', plain,
% 0.61/0.80      (![X56 : $i, X57 : $i]:
% 0.61/0.80         (((k7_relat_1 @ X57 @ X56) = (k5_relat_1 @ (k6_relat_1 @ X56) @ X57))
% 0.61/0.80          | ~ (v1_relat_1 @ X57))),
% 0.61/0.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.61/0.80  thf('74', plain,
% 0.61/0.80      (![X48 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X48)) = (k6_relat_1 @ X48))),
% 0.61/0.80      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.61/0.80  thf('75', plain,
% 0.61/0.80      (![X44 : $i, X45 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X44)
% 0.61/0.80          | ((k4_relat_1 @ (k5_relat_1 @ X45 @ X44))
% 0.61/0.80              = (k5_relat_1 @ (k4_relat_1 @ X44) @ (k4_relat_1 @ X45)))
% 0.61/0.80          | ~ (v1_relat_1 @ X45))),
% 0.61/0.80      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.61/0.80  thf('76', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.61/0.80          | ~ (v1_relat_1 @ X1)
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['74', '75'])).
% 0.61/0.80  thf('77', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('78', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.61/0.80          | ~ (v1_relat_1 @ X1))),
% 0.61/0.80      inference('demod', [status(thm)], ['76', '77'])).
% 0.61/0.80  thf('79', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.61/0.80            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.61/0.80               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['73', '78'])).
% 0.61/0.80  thf('80', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.61/0.80  thf('81', plain,
% 0.61/0.80      (![X48 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X48)) = (k6_relat_1 @ X48))),
% 0.61/0.80      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.61/0.80  thf('82', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('83', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('84', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.61/0.80  thf('85', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.61/0.80            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['72', '84'])).
% 0.61/0.80  thf('86', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('87', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['85', '86'])).
% 0.61/0.80  thf('88', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['85', '86'])).
% 0.61/0.80  thf('89', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.80  thf('90', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.61/0.80           = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 0.61/0.80              (k6_relat_1 @ X1)))),
% 0.61/0.80      inference('demod', [status(thm)], ['71', '87', '88', '89'])).
% 0.61/0.80  thf('91', plain,
% 0.61/0.80      (![X42 : $i, X43 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X42)
% 0.61/0.80          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X43 @ X42)) @ 
% 0.61/0.80             (k2_relat_1 @ X42))
% 0.61/0.80          | ~ (v1_relat_1 @ X43))),
% 0.61/0.80      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.61/0.80  thf('92', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.61/0.80           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.61/0.80          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['90', '91'])).
% 0.61/0.80  thf('93', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['22', '23'])).
% 0.61/0.80  thf('94', plain, (![X47 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 0.61/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.80  thf('95', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.80  thf('96', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('97', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 0.61/0.80      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.61/0.80  thf('98', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (r1_tarski @ X0 @ X1)
% 0.61/0.80          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['41', '42'])).
% 0.61/0.80  thf('99', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k8_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.61/0.80           (k6_relat_1 @ X0))
% 0.61/0.80           = (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['97', '98'])).
% 0.61/0.80  thf('100', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.80  thf('101', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['22', '23'])).
% 0.61/0.80  thf('102', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('103', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)],
% 0.61/0.80                ['19', '24', '25', '44', '45', '99', '100', '101', '102'])).
% 0.61/0.80  thf('104', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)],
% 0.61/0.80                ['19', '24', '25', '44', '45', '99', '100', '101', '102'])).
% 0.61/0.80  thf('105', plain, (![X46 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.61/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.80  thf('106', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['104', '105'])).
% 0.61/0.80  thf('107', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.61/0.80  thf(t90_relat_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ B ) =>
% 0.61/0.80       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.61/0.80         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.61/0.80  thf('108', plain,
% 0.61/0.80      (![X54 : $i, X55 : $i]:
% 0.61/0.80         (((k1_relat_1 @ (k7_relat_1 @ X54 @ X55))
% 0.61/0.80            = (k3_xboole_0 @ (k1_relat_1 @ X54) @ X55))
% 0.61/0.80          | ~ (v1_relat_1 @ X54))),
% 0.61/0.80      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.61/0.80  thf('109', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 0.61/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['107', '108'])).
% 0.61/0.80  thf('110', plain, (![X46 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.61/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.80  thf('111', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('112', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.61/0.80           = (k3_xboole_0 @ X1 @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.61/0.80  thf('113', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['106', '112'])).
% 0.61/0.80  thf('114', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.61/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['103', '113'])).
% 0.61/0.80  thf('115', plain,
% 0.61/0.80      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.61/0.80         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.61/0.80      inference('demod', [status(thm)], ['4', '114'])).
% 0.61/0.80  thf('116', plain, ($false), inference('simplify', [status(thm)], ['115'])).
% 0.61/0.80  
% 0.61/0.80  % SZS output end Refutation
% 0.61/0.80  
% 0.61/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
