%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z0jYKDrlqu

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:24 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 267 expanded)
%              Number of leaves         :   37 ( 102 expanded)
%              Depth                    :   29
%              Number of atoms          :  858 (2164 expanded)
%              Number of equality atoms :   76 ( 184 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X72: $i,X73: $i,X74: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X73 @ X72 ) @ X74 )
        = ( k3_xboole_0 @ X72 @ ( k10_relat_1 @ X73 @ X74 ) ) )
      | ~ ( v1_relat_1 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X72: $i,X73: $i,X74: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X73 @ X72 ) @ X74 )
        = ( k1_setfam_1 @ ( k2_tarski @ X72 @ ( k10_relat_1 @ X73 @ X74 ) ) ) )
      | ~ ( v1_relat_1 @ X73 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( r1_tarski @ X55 @ X56 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X57 @ X56 ) @ X55 )
        = ( k9_relat_1 @ X57 @ X55 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('10',plain,(
    ! [X70: $i,X71: $i] :
      ( ( ( k7_relat_1 @ X71 @ X70 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X70 ) @ X71 ) )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v1_relat_1 @ X64 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X65 @ X64 ) )
        = ( k10_relat_1 @ X65 @ ( k1_relat_1 @ X64 ) ) )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16
        = ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('15',plain,(
    ! [X67: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X67 ) )
      = X67 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X60: $i] :
      ( ( ( k10_relat_1 @ X60 @ ( k2_relat_1 @ X60 ) )
        = ( k1_relat_1 @ X60 ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X66: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('19',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( ( k10_relat_1 @ X61 @ ( k2_xboole_0 @ X62 @ X63 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X61 @ X62 ) @ ( k10_relat_1 @ X61 @ X63 ) ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
        = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X58 @ X59 ) @ ( k1_relat_1 @ X58 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X1 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X66: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    ! [X66: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('34',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['24','35'])).

thf('37',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['14','36'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','37'])).

thf('39',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X54: $i] :
      ( ( ( k9_relat_1 @ X54 @ ( k1_relat_1 @ X54 ) )
        = ( k2_relat_1 @ X54 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('46',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X60: $i] :
      ( ( ( k10_relat_1 @ X60 @ ( k2_relat_1 @ X60 ) )
        = ( k1_relat_1 @ X60 ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('54',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('56',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('68',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('73',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['66','75'])).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z0jYKDrlqu
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.10  % Solved by: fo/fo7.sh
% 0.90/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.10  % done 1466 iterations in 0.610s
% 0.90/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.10  % SZS output start Refutation
% 0.90/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.10  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.90/1.10  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.10  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.90/1.10  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.90/1.10  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.90/1.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.10  thf(t146_funct_1, conjecture,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ B ) =>
% 0.90/1.10       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.90/1.10         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.10    (~( ![A:$i,B:$i]:
% 0.90/1.10        ( ( v1_relat_1 @ B ) =>
% 0.90/1.10          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.90/1.10            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.90/1.10    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.90/1.10  thf('0', plain,
% 0.90/1.10      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t139_funct_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ C ) =>
% 0.90/1.10       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.90/1.10         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.90/1.10  thf('1', plain,
% 0.90/1.10      (![X72 : $i, X73 : $i, X74 : $i]:
% 0.90/1.10         (((k10_relat_1 @ (k7_relat_1 @ X73 @ X72) @ X74)
% 0.90/1.10            = (k3_xboole_0 @ X72 @ (k10_relat_1 @ X73 @ X74)))
% 0.90/1.10          | ~ (v1_relat_1 @ X73))),
% 0.90/1.10      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.90/1.10  thf(t12_setfam_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.90/1.10  thf('2', plain,
% 0.90/1.10      (![X49 : $i, X50 : $i]:
% 0.90/1.10         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.90/1.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.90/1.10  thf('3', plain,
% 0.90/1.10      (![X72 : $i, X73 : $i, X74 : $i]:
% 0.90/1.10         (((k10_relat_1 @ (k7_relat_1 @ X73 @ X72) @ X74)
% 0.90/1.10            = (k1_setfam_1 @ (k2_tarski @ X72 @ (k10_relat_1 @ X73 @ X74))))
% 0.90/1.10          | ~ (v1_relat_1 @ X73))),
% 0.90/1.10      inference('demod', [status(thm)], ['1', '2'])).
% 0.90/1.10  thf(dt_k7_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.90/1.10  thf('4', plain,
% 0.90/1.10      (![X52 : $i, X53 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X52) | (v1_relat_1 @ (k7_relat_1 @ X52 @ X53)))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.90/1.10  thf(d10_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.10  thf('5', plain,
% 0.90/1.10      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('6', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.90/1.10      inference('simplify', [status(thm)], ['5'])).
% 0.90/1.10  thf(t162_relat_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ A ) =>
% 0.90/1.10       ( ![B:$i,C:$i]:
% 0.90/1.10         ( ( r1_tarski @ B @ C ) =>
% 0.90/1.10           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.90/1.10             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.90/1.10  thf('7', plain,
% 0.90/1.10      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X55 @ X56)
% 0.90/1.10          | ((k9_relat_1 @ (k7_relat_1 @ X57 @ X56) @ X55)
% 0.90/1.10              = (k9_relat_1 @ X57 @ X55))
% 0.90/1.10          | ~ (v1_relat_1 @ X57))),
% 0.90/1.10      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.90/1.10  thf('8', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X1)
% 0.90/1.10          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.90/1.10              = (k9_relat_1 @ X1 @ X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.10  thf('9', plain,
% 0.90/1.10      (![X52 : $i, X53 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X52) | (v1_relat_1 @ (k7_relat_1 @ X52 @ X53)))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.90/1.10  thf(t94_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ B ) =>
% 0.90/1.10       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.90/1.10  thf('10', plain,
% 0.90/1.10      (![X70 : $i, X71 : $i]:
% 0.90/1.10         (((k7_relat_1 @ X71 @ X70) = (k5_relat_1 @ (k6_relat_1 @ X70) @ X71))
% 0.90/1.10          | ~ (v1_relat_1 @ X71))),
% 0.90/1.10      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.90/1.10  thf(t182_relat_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( v1_relat_1 @ B ) =>
% 0.90/1.10           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.90/1.10             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.90/1.10  thf('11', plain,
% 0.90/1.10      (![X64 : $i, X65 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X64)
% 0.90/1.10          | ((k1_relat_1 @ (k5_relat_1 @ X65 @ X64))
% 0.90/1.10              = (k10_relat_1 @ X65 @ (k1_relat_1 @ X64)))
% 0.90/1.10          | ~ (v1_relat_1 @ X65))),
% 0.90/1.10      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.90/1.10  thf('12', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t45_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( r1_tarski @ A @ B ) =>
% 0.90/1.10       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.90/1.10  thf('13', plain,
% 0.90/1.10      (![X15 : $i, X16 : $i]:
% 0.90/1.10         (((X16) = (k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))
% 0.90/1.10          | ~ (r1_tarski @ X15 @ X16))),
% 0.90/1.10      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.90/1.10  thf('14', plain,
% 0.90/1.10      (((k1_relat_1 @ sk_B)
% 0.90/1.10         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.10  thf(t71_relat_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.90/1.10       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.90/1.10  thf('15', plain, (![X67 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X67)) = (X67))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf(t169_relat_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ A ) =>
% 0.90/1.10       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.90/1.10  thf('16', plain,
% 0.90/1.10      (![X60 : $i]:
% 0.90/1.10         (((k10_relat_1 @ X60 @ (k2_relat_1 @ X60)) = (k1_relat_1 @ X60))
% 0.90/1.10          | ~ (v1_relat_1 @ X60))),
% 0.90/1.10      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.90/1.10  thf('17', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.90/1.10            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['15', '16'])).
% 0.90/1.10  thf('18', plain, (![X66 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X66)) = (X66))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.90/1.10  thf('19', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('20', plain,
% 0.90/1.10      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.90/1.10  thf(t175_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ C ) =>
% 0.90/1.10       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.90/1.10         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.90/1.10  thf('21', plain,
% 0.90/1.10      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.90/1.10         (((k10_relat_1 @ X61 @ (k2_xboole_0 @ X62 @ X63))
% 0.90/1.10            = (k2_xboole_0 @ (k10_relat_1 @ X61 @ X62) @ 
% 0.90/1.10               (k10_relat_1 @ X61 @ X63)))
% 0.90/1.10          | ~ (v1_relat_1 @ X61))),
% 0.90/1.10      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.90/1.10  thf('22', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 0.90/1.10            = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['20', '21'])).
% 0.90/1.10  thf('23', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('24', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 0.90/1.10           = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['22', '23'])).
% 0.90/1.10  thf('25', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 0.90/1.10           = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['22', '23'])).
% 0.90/1.10  thf(t167_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ B ) =>
% 0.90/1.10       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.90/1.10  thf('26', plain,
% 0.90/1.10      (![X58 : $i, X59 : $i]:
% 0.90/1.10         ((r1_tarski @ (k10_relat_1 @ X58 @ X59) @ (k1_relat_1 @ X58))
% 0.90/1.10          | ~ (v1_relat_1 @ X58))),
% 0.90/1.10      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.90/1.10  thf('27', plain,
% 0.90/1.10      (![X1 : $i, X3 : $i]:
% 0.90/1.10         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('28', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X0)
% 0.90/1.10          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.90/1.10          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.10  thf('29', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ 
% 0.90/1.10             (k2_xboole_0 @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.90/1.10          | ((k1_relat_1 @ (k6_relat_1 @ X1))
% 0.90/1.10              = (k10_relat_1 @ (k6_relat_1 @ X1) @ (k2_xboole_0 @ X1 @ X0)))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['25', '28'])).
% 0.90/1.10  thf('30', plain, (![X66 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X66)) = (X66))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf(t7_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.10  thf('31', plain,
% 0.90/1.10      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.90/1.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.10  thf('32', plain, (![X66 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X66)) = (X66))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('33', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 0.90/1.10           = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['22', '23'])).
% 0.90/1.10  thf('34', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('35', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((X1) = (k2_xboole_0 @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['29', '30', '31', '32', '33', '34'])).
% 0.90/1.10  thf('36', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['24', '35'])).
% 0.90/1.10  thf('37', plain,
% 0.90/1.10      (((k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.90/1.10      inference('sup+', [status(thm)], ['14', '36'])).
% 0.90/1.10  thf('38', plain,
% 0.90/1.10      ((((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))
% 0.90/1.10        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.90/1.10        | ~ (v1_relat_1 @ sk_B))),
% 0.90/1.10      inference('sup+', [status(thm)], ['11', '37'])).
% 0.90/1.10  thf('39', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('41', plain,
% 0.90/1.10      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.90/1.10  thf('42', plain,
% 0.90/1.10      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.90/1.10        | ~ (v1_relat_1 @ sk_B))),
% 0.90/1.10      inference('sup+', [status(thm)], ['10', '41'])).
% 0.90/1.10  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('44', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['42', '43'])).
% 0.90/1.10  thf(t146_relat_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ A ) =>
% 0.90/1.10       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.90/1.10  thf('45', plain,
% 0.90/1.10      (![X54 : $i]:
% 0.90/1.10         (((k9_relat_1 @ X54 @ (k1_relat_1 @ X54)) = (k2_relat_1 @ X54))
% 0.90/1.10          | ~ (v1_relat_1 @ X54))),
% 0.90/1.10      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.90/1.10  thf('46', plain,
% 0.90/1.10      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.90/1.10          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.90/1.10        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['44', '45'])).
% 0.90/1.10  thf('47', plain,
% 0.90/1.10      ((~ (v1_relat_1 @ sk_B)
% 0.90/1.10        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.90/1.10            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['9', '46'])).
% 0.90/1.10  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('49', plain,
% 0.90/1.10      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.90/1.10         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['47', '48'])).
% 0.90/1.10  thf('50', plain,
% 0.90/1.10      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.90/1.10        | ~ (v1_relat_1 @ sk_B))),
% 0.90/1.10      inference('sup+', [status(thm)], ['8', '49'])).
% 0.90/1.10  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('52', plain,
% 0.90/1.10      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['50', '51'])).
% 0.90/1.10  thf('53', plain,
% 0.90/1.10      (![X60 : $i]:
% 0.90/1.10         (((k10_relat_1 @ X60 @ (k2_relat_1 @ X60)) = (k1_relat_1 @ X60))
% 0.90/1.10          | ~ (v1_relat_1 @ X60))),
% 0.90/1.10      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.90/1.10  thf('54', plain,
% 0.90/1.10      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.90/1.10          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.90/1.10        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['52', '53'])).
% 0.90/1.10  thf('55', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['42', '43'])).
% 0.90/1.10  thf('56', plain,
% 0.90/1.10      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.90/1.10          = (sk_A))
% 0.90/1.10        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['54', '55'])).
% 0.90/1.10  thf('57', plain,
% 0.90/1.10      ((~ (v1_relat_1 @ sk_B)
% 0.90/1.10        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.90/1.10            (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['4', '56'])).
% 0.90/1.10  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('59', plain,
% 0.90/1.10      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.90/1.10         = (sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['57', '58'])).
% 0.90/1.10  thf('60', plain,
% 0.90/1.10      ((((k1_setfam_1 @ 
% 0.90/1.10          (k2_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.90/1.10          = (sk_A))
% 0.90/1.10        | ~ (v1_relat_1 @ sk_B))),
% 0.90/1.10      inference('sup+', [status(thm)], ['3', '59'])).
% 0.90/1.10  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('62', plain,
% 0.90/1.10      (((k1_setfam_1 @ 
% 0.90/1.10         (k2_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.90/1.10         = (sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['60', '61'])).
% 0.90/1.10  thf(t100_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.10  thf('63', plain,
% 0.90/1.10      (![X7 : $i, X8 : $i]:
% 0.90/1.10         ((k4_xboole_0 @ X7 @ X8)
% 0.90/1.10           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.10  thf('64', plain,
% 0.90/1.10      (![X49 : $i, X50 : $i]:
% 0.90/1.10         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.90/1.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.90/1.10  thf('65', plain,
% 0.90/1.10      (![X7 : $i, X8 : $i]:
% 0.90/1.10         ((k4_xboole_0 @ X7 @ X8)
% 0.90/1.10           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 0.90/1.10      inference('demod', [status(thm)], ['63', '64'])).
% 0.90/1.10  thf('66', plain,
% 0.90/1.10      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.90/1.10         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.90/1.10      inference('sup+', [status(thm)], ['62', '65'])).
% 0.90/1.10  thf(idempotence_k3_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.90/1.10  thf('67', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.90/1.10      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.90/1.10  thf('68', plain,
% 0.90/1.10      (![X49 : $i, X50 : $i]:
% 0.90/1.10         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.90/1.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.90/1.10  thf('69', plain,
% 0.90/1.10      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['67', '68'])).
% 0.90/1.10  thf('70', plain,
% 0.90/1.10      (![X7 : $i, X8 : $i]:
% 0.90/1.10         ((k4_xboole_0 @ X7 @ X8)
% 0.90/1.10           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 0.90/1.10      inference('demod', [status(thm)], ['63', '64'])).
% 0.90/1.10  thf('71', plain,
% 0.90/1.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.10      inference('sup+', [status(thm)], ['69', '70'])).
% 0.90/1.10  thf('72', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.90/1.10      inference('simplify', [status(thm)], ['5'])).
% 0.90/1.10  thf(l32_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.10  thf('73', plain,
% 0.90/1.10      (![X4 : $i, X6 : $i]:
% 0.90/1.10         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.90/1.10      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.90/1.10  thf('74', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['72', '73'])).
% 0.90/1.10  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.10      inference('sup+', [status(thm)], ['71', '74'])).
% 0.90/1.10  thf('76', plain,
% 0.90/1.10      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.90/1.10         = (k1_xboole_0))),
% 0.90/1.10      inference('demod', [status(thm)], ['66', '75'])).
% 0.90/1.10  thf('77', plain,
% 0.90/1.10      (![X4 : $i, X5 : $i]:
% 0.90/1.10         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.90/1.10      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.90/1.10  thf('78', plain,
% 0.90/1.10      ((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.10        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['76', '77'])).
% 0.90/1.10  thf('79', plain,
% 0.90/1.10      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('simplify', [status(thm)], ['78'])).
% 0.90/1.10  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.90/1.10  
% 0.90/1.10  % SZS output end Refutation
% 0.90/1.10  
% 0.90/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
