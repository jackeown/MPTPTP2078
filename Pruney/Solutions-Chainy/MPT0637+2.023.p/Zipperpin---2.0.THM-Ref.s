%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2rQsitNGnn

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:58 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  177 (2649 expanded)
%              Number of leaves         :   30 ( 953 expanded)
%              Depth                    :   21
%              Number of atoms          : 1504 (21664 expanded)
%              Number of equality atoms :  121 (1798 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
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
    ! [X28: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ ( k1_relat_1 @ X37 ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('16',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('26',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','30'])).

thf('32',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('33',plain,(
    ! [X30: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X30 ) )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X27 @ X26 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X26 ) @ ( k4_relat_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('40',plain,(
    ! [X30: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X30 ) )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) ) @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('50',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) ) @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('53',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['48','60'])).

thf('62',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','63','64','65'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ ( k1_relat_1 @ X37 ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('71',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('72',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X31 ) @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('81',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('82',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) ) @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','84'])).

thf('86',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('91',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('92',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('100',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('106',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['103','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k8_relat_1 @ X0 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['98','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('114',plain,(
    ! [X28: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('116',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('117',plain,(
    ! [X28: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('118',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['69','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['103','110'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
        = ( k8_relat_1 @ X1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('129',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('130',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','63','64','65'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['122','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','63','64','65'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','143'])).

thf('145',plain,(
    $false ),
    inference(simplify,[status(thm)],['144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2rQsitNGnn
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.14  % Solved by: fo/fo7.sh
% 0.91/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.14  % done 991 iterations in 0.683s
% 0.91/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.14  % SZS output start Refutation
% 0.91/1.14  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.14  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.91/1.14  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.91/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.14  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.91/1.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.91/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.14  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.91/1.14  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.91/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.91/1.14  thf(t123_relat_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ B ) =>
% 0.91/1.14       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.91/1.14  thf('0', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i]:
% 0.91/1.14         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 0.91/1.14          | ~ (v1_relat_1 @ X20))),
% 0.91/1.14      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.91/1.14  thf(t43_funct_1, conjecture,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.91/1.14       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.14    (~( ![A:$i,B:$i]:
% 0.91/1.14        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.91/1.14          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.91/1.14    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.91/1.14  thf('1', plain,
% 0.91/1.14      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.91/1.14         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('2', plain,
% 0.91/1.14      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.91/1.14          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.91/1.14        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.14  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.91/1.14  thf('3', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('4', plain,
% 0.91/1.14      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.91/1.14         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.91/1.14      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.14  thf(commutativity_k2_tarski, axiom,
% 0.91/1.14    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.91/1.14  thf('5', plain,
% 0.91/1.14      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.91/1.14      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.91/1.14  thf(t12_setfam_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.91/1.14  thf('6', plain,
% 0.91/1.14      (![X9 : $i, X10 : $i]:
% 0.91/1.14         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.91/1.14      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.91/1.14  thf('7', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['5', '6'])).
% 0.91/1.14  thf('8', plain,
% 0.91/1.14      (![X9 : $i, X10 : $i]:
% 0.91/1.14         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.91/1.14      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.91/1.14  thf('9', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf(t71_relat_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.91/1.14       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.91/1.14  thf('10', plain, (![X28 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 0.91/1.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.14  thf(t98_relat_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ A ) =>
% 0.91/1.14       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.91/1.14  thf('11', plain,
% 0.91/1.14      (![X37 : $i]:
% 0.91/1.14         (((k7_relat_1 @ X37 @ (k1_relat_1 @ X37)) = (X37))
% 0.91/1.14          | ~ (v1_relat_1 @ X37))),
% 0.91/1.14      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.91/1.14  thf('12', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['10', '11'])).
% 0.91/1.14  thf('13', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('14', plain,
% 0.91/1.14      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['12', '13'])).
% 0.91/1.14  thf('15', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i]:
% 0.91/1.14         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 0.91/1.14          | ~ (v1_relat_1 @ X20))),
% 0.91/1.14      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.91/1.14  thf(t94_relat_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ B ) =>
% 0.91/1.14       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.91/1.14  thf('16', plain,
% 0.91/1.14      (![X33 : $i, X34 : $i]:
% 0.91/1.14         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 0.91/1.14          | ~ (v1_relat_1 @ X34))),
% 0.91/1.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.91/1.14  thf('17', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['15', '16'])).
% 0.91/1.14  thf('18', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('19', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('20', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.14  thf('21', plain,
% 0.91/1.14      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['14', '20'])).
% 0.91/1.14  thf('22', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.14  thf(t100_relat_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ C ) =>
% 0.91/1.14       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.91/1.14         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.91/1.14  thf('23', plain,
% 0.91/1.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.14         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 0.91/1.14            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 0.91/1.14          | ~ (v1_relat_1 @ X14))),
% 0.91/1.14      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.91/1.14  thf('24', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.91/1.14            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['22', '23'])).
% 0.91/1.14  thf('25', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.14  thf('26', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('27', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.91/1.14      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.91/1.14  thf('28', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.91/1.14           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.91/1.14      inference('sup+', [status(thm)], ['21', '27'])).
% 0.91/1.14  thf('29', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.14  thf('30', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.91/1.14           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.91/1.14      inference('demod', [status(thm)], ['28', '29'])).
% 0.91/1.14  thf('31', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.91/1.14           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.91/1.14      inference('sup+', [status(thm)], ['9', '30'])).
% 0.91/1.14  thf('32', plain,
% 0.91/1.14      (![X33 : $i, X34 : $i]:
% 0.91/1.14         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 0.91/1.14          | ~ (v1_relat_1 @ X34))),
% 0.91/1.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.91/1.14  thf(t72_relat_1, axiom,
% 0.91/1.14    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.91/1.14  thf('33', plain,
% 0.91/1.14      (![X30 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X30)) = (k6_relat_1 @ X30))),
% 0.91/1.14      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.91/1.14  thf(t54_relat_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ A ) =>
% 0.91/1.14       ( ![B:$i]:
% 0.91/1.14         ( ( v1_relat_1 @ B ) =>
% 0.91/1.14           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.91/1.14             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.91/1.14  thf('34', plain,
% 0.91/1.14      (![X26 : $i, X27 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X26)
% 0.91/1.14          | ((k4_relat_1 @ (k5_relat_1 @ X27 @ X26))
% 0.91/1.14              = (k5_relat_1 @ (k4_relat_1 @ X26) @ (k4_relat_1 @ X27)))
% 0.91/1.14          | ~ (v1_relat_1 @ X27))),
% 0.91/1.14      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.91/1.14  thf('35', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.91/1.14            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.91/1.14          | ~ (v1_relat_1 @ X1)
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['33', '34'])).
% 0.91/1.14  thf('36', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('37', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.91/1.14            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.91/1.14          | ~ (v1_relat_1 @ X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['35', '36'])).
% 0.91/1.14  thf('38', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.91/1.14            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.91/1.14               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['32', '37'])).
% 0.91/1.14  thf('39', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.14  thf('40', plain,
% 0.91/1.14      (![X30 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X30)) = (k6_relat_1 @ X30))),
% 0.91/1.14      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.91/1.14  thf('41', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i]:
% 0.91/1.14         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 0.91/1.14          | ~ (v1_relat_1 @ X20))),
% 0.91/1.14      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.91/1.14  thf(t76_relat_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ B ) =>
% 0.91/1.14       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.91/1.14         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.91/1.14  thf('42', plain,
% 0.91/1.14      (![X31 : $i, X32 : $i]:
% 0.91/1.14         ((r1_tarski @ (k5_relat_1 @ X31 @ (k6_relat_1 @ X32)) @ X31)
% 0.91/1.14          | ~ (v1_relat_1 @ X31))),
% 0.91/1.14      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.91/1.14  thf(t28_xboole_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.91/1.14  thf('43', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.14  thf('44', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X0)
% 0.91/1.14          | ((k3_xboole_0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 0.91/1.14              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.14  thf('45', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('46', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X0)
% 0.91/1.14          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.91/1.14              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.91/1.14      inference('demod', [status(thm)], ['44', '45'])).
% 0.91/1.14  thf('47', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X0 @ (k8_relat_1 @ X1 @ X0))
% 0.91/1.14            = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.91/1.14          | ~ (v1_relat_1 @ X0)
% 0.91/1.14          | ~ (v1_relat_1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['41', '46'])).
% 0.91/1.14  thf('48', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X0)
% 0.91/1.14          | ((k3_xboole_0 @ X0 @ (k8_relat_1 @ X1 @ X0))
% 0.91/1.14              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.91/1.14      inference('simplify', [status(thm)], ['47'])).
% 0.91/1.14  thf('49', plain,
% 0.91/1.14      (![X33 : $i, X34 : $i]:
% 0.91/1.14         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 0.91/1.14          | ~ (v1_relat_1 @ X34))),
% 0.91/1.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.91/1.14  thf('50', plain,
% 0.91/1.14      (![X31 : $i, X32 : $i]:
% 0.91/1.14         ((r1_tarski @ (k5_relat_1 @ X31 @ (k6_relat_1 @ X32)) @ X31)
% 0.91/1.14          | ~ (v1_relat_1 @ X31))),
% 0.91/1.14      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.91/1.14  thf('51', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.91/1.14           (k6_relat_1 @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['49', '50'])).
% 0.91/1.14  thf('52', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('53', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('54', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.91/1.14  thf('55', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.14  thf('56', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['54', '55'])).
% 0.91/1.14  thf('57', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.14  thf('58', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k3_xboole_0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.91/1.14           (k6_relat_1 @ X0)) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['56', '57'])).
% 0.91/1.14  thf('59', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('60', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 0.91/1.14           (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['58', '59'])).
% 0.91/1.14  thf('61', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.91/1.14            = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['48', '60'])).
% 0.91/1.14  thf('62', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('63', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.91/1.14           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('demod', [status(thm)], ['61', '62'])).
% 0.91/1.14  thf('64', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('65', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('66', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.91/1.14           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('demod', [status(thm)], ['38', '39', '40', '63', '64', '65'])).
% 0.91/1.14  thf('67', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.91/1.14           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['31', '66'])).
% 0.91/1.14  thf('68', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.91/1.14           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('demod', [status(thm)], ['38', '39', '40', '63', '64', '65'])).
% 0.91/1.14  thf('69', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.91/1.14           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('demod', [status(thm)], ['67', '68'])).
% 0.91/1.14  thf('70', plain,
% 0.91/1.14      (![X37 : $i]:
% 0.91/1.14         (((k7_relat_1 @ X37 @ (k1_relat_1 @ X37)) = (X37))
% 0.91/1.14          | ~ (v1_relat_1 @ X37))),
% 0.91/1.14      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.91/1.14  thf('71', plain,
% 0.91/1.14      (![X33 : $i, X34 : $i]:
% 0.91/1.14         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 0.91/1.14          | ~ (v1_relat_1 @ X34))),
% 0.91/1.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.91/1.14  thf('72', plain,
% 0.91/1.14      (![X31 : $i, X32 : $i]:
% 0.91/1.14         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X32) @ X31) @ X31)
% 0.91/1.14          | ~ (v1_relat_1 @ X31))),
% 0.91/1.14      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.91/1.14  thf('73', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.14  thf('74', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X0)
% 0.91/1.14          | ((k3_xboole_0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 0.91/1.14              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['72', '73'])).
% 0.91/1.14  thf('75', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('76', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X0)
% 0.91/1.14          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.91/1.14              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['74', '75'])).
% 0.91/1.14  thf('77', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))
% 0.91/1.14            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.91/1.14          | ~ (v1_relat_1 @ X1)
% 0.91/1.14          | ~ (v1_relat_1 @ X1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['71', '76'])).
% 0.91/1.14  thf('78', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X1)
% 0.91/1.14          | ((k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))
% 0.91/1.14              = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['77'])).
% 0.91/1.14  thf('79', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X0 @ X0)
% 0.91/1.14            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ X0)
% 0.91/1.14          | ~ (v1_relat_1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['70', '78'])).
% 0.91/1.14  thf('80', plain,
% 0.91/1.14      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['14', '20'])).
% 0.91/1.14  thf('81', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i]:
% 0.91/1.14         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 0.91/1.14          | ~ (v1_relat_1 @ X20))),
% 0.91/1.14      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.91/1.14  thf('82', plain,
% 0.91/1.14      (![X31 : $i, X32 : $i]:
% 0.91/1.14         ((r1_tarski @ (k5_relat_1 @ X31 @ (k6_relat_1 @ X32)) @ X31)
% 0.91/1.14          | ~ (v1_relat_1 @ X31))),
% 0.91/1.14      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.91/1.14  thf('83', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.91/1.14          | ~ (v1_relat_1 @ X0)
% 0.91/1.14          | ~ (v1_relat_1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['81', '82'])).
% 0.91/1.14  thf('84', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 0.91/1.14      inference('simplify', [status(thm)], ['83'])).
% 0.91/1.14  thf('85', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         ((r1_tarski @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['80', '84'])).
% 0.91/1.14  thf('86', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('87', plain,
% 0.91/1.14      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['85', '86'])).
% 0.91/1.14  thf(t25_relat_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ A ) =>
% 0.91/1.14       ( ![B:$i]:
% 0.91/1.14         ( ( v1_relat_1 @ B ) =>
% 0.91/1.14           ( ( r1_tarski @ A @ B ) =>
% 0.91/1.14             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.91/1.14               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.91/1.14  thf('88', plain,
% 0.91/1.14      (![X24 : $i, X25 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X24)
% 0.91/1.14          | (r1_tarski @ (k2_relat_1 @ X25) @ (k2_relat_1 @ X24))
% 0.91/1.14          | ~ (r1_tarski @ X25 @ X24)
% 0.91/1.14          | ~ (v1_relat_1 @ X25))),
% 0.91/1.14      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.91/1.14  thf('89', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.91/1.14          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.91/1.14             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['87', '88'])).
% 0.91/1.14  thf('90', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('91', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.91/1.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.14  thf('92', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.91/1.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.14  thf('93', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('94', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.91/1.14      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 0.91/1.14  thf('95', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.14  thf('96', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['94', '95'])).
% 0.91/1.14  thf('97', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (((X0) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ X0)
% 0.91/1.14          | ~ (v1_relat_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['79', '96'])).
% 0.91/1.14  thf('98', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X0)
% 0.91/1.14          | ((X0) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['97'])).
% 0.91/1.14  thf('99', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i]:
% 0.91/1.14         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 0.91/1.14          | ~ (v1_relat_1 @ X20))),
% 0.91/1.14      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.91/1.14  thf(t112_relat_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ B ) =>
% 0.91/1.14       ( ![C:$i]:
% 0.91/1.14         ( ( v1_relat_1 @ C ) =>
% 0.91/1.14           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.91/1.14             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.91/1.14  thf('100', plain,
% 0.91/1.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X17)
% 0.91/1.14          | ((k7_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 0.91/1.14              = (k5_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X17))
% 0.91/1.14          | ~ (v1_relat_1 @ X18))),
% 0.91/1.14      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.91/1.14  thf('101', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 0.91/1.14            = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.91/1.14          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ X1)
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['99', '100'])).
% 0.91/1.14  thf('102', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('103', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 0.91/1.14            = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.91/1.14          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['101', '102'])).
% 0.91/1.14  thf('104', plain,
% 0.91/1.14      (![X33 : $i, X34 : $i]:
% 0.91/1.14         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 0.91/1.14          | ~ (v1_relat_1 @ X34))),
% 0.91/1.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.91/1.14  thf('105', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X0)
% 0.91/1.14          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.91/1.14              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['74', '75'])).
% 0.91/1.14  thf(fc1_relat_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.14  thf('106', plain,
% 0.91/1.14      (![X12 : $i, X13 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.91/1.14      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.91/1.14  thf('107', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ X0)
% 0.91/1.14          | ~ (v1_relat_1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['105', '106'])).
% 0.91/1.14  thf('108', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X0)
% 0.91/1.14          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['107'])).
% 0.91/1.14  thf('109', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ X1)
% 0.91/1.14          | ~ (v1_relat_1 @ X1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['104', '108'])).
% 0.91/1.14  thf('110', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['109'])).
% 0.91/1.14  thf('111', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X1)
% 0.91/1.14          | ((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 0.91/1.14              = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))))),
% 0.91/1.14      inference('clc', [status(thm)], ['103', '110'])).
% 0.91/1.14  thf('112', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.91/1.14            = (k8_relat_1 @ X0 @ 
% 0.91/1.14               (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))) @ 
% 0.91/1.14                X1)))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))),
% 0.91/1.14      inference('sup+', [status(thm)], ['98', '111'])).
% 0.91/1.14  thf('113', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.14  thf('114', plain, (![X28 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 0.91/1.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.14  thf('115', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.14  thf('116', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('117', plain, (![X28 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 0.91/1.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.14  thf('118', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('119', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.91/1.14           = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.91/1.14      inference('demod', [status(thm)],
% 0.91/1.14                ['112', '113', '114', '115', '116', '117', '118'])).
% 0.91/1.14  thf('120', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X0))
% 0.91/1.14           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.91/1.14              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.91/1.14      inference('sup+', [status(thm)], ['69', '119'])).
% 0.91/1.14  thf('121', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.91/1.14           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('demod', [status(thm)], ['67', '68'])).
% 0.91/1.14  thf('122', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.91/1.14           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.91/1.14              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.91/1.14      inference('demod', [status(thm)], ['120', '121'])).
% 0.91/1.14  thf('123', plain,
% 0.91/1.14      (![X33 : $i, X34 : $i]:
% 0.91/1.14         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 0.91/1.14          | ~ (v1_relat_1 @ X34))),
% 0.91/1.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.91/1.14  thf('124', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X1)
% 0.91/1.14          | ((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 0.91/1.14              = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))))),
% 0.91/1.14      inference('clc', [status(thm)], ['103', '110'])).
% 0.91/1.14  thf('125', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.91/1.14            = (k8_relat_1 @ X1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2)))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.91/1.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['123', '124'])).
% 0.91/1.14  thf('126', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.14  thf('127', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.91/1.14      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.91/1.14  thf('128', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.14  thf('129', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('130', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.14  thf('131', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2)))
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2))))),
% 0.91/1.14      inference('demod', [status(thm)],
% 0.91/1.14                ['125', '126', '127', '128', '129', '130'])).
% 0.91/1.14  thf('132', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.91/1.14           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('demod', [status(thm)], ['38', '39', '40', '63', '64', '65'])).
% 0.91/1.14  thf('133', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k4_relat_1 @ 
% 0.91/1.14           (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.91/1.14           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X2)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['131', '132'])).
% 0.91/1.14  thf('134', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.91/1.14           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.91/1.14              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.91/1.14      inference('sup+', [status(thm)], ['122', '133'])).
% 0.91/1.14  thf('135', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.91/1.14           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.91/1.14      inference('demod', [status(thm)], ['38', '39', '40', '63', '64', '65'])).
% 0.91/1.14  thf('136', plain,
% 0.91/1.14      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['14', '20'])).
% 0.91/1.14  thf('137', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.91/1.14           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.91/1.14  thf('138', plain,
% 0.91/1.14      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.91/1.14         != (k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))),
% 0.91/1.14      inference('demod', [status(thm)], ['4', '137'])).
% 0.91/1.14  thf('139', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('140', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.91/1.14           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.91/1.14  thf('141', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.91/1.14           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['139', '140'])).
% 0.91/1.14  thf('142', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.91/1.14           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.91/1.14  thf('143', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.91/1.14           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['141', '142'])).
% 0.91/1.14  thf('144', plain,
% 0.91/1.14      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.91/1.14         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.91/1.14      inference('demod', [status(thm)], ['138', '143'])).
% 0.91/1.14  thf('145', plain, ($false), inference('simplify', [status(thm)], ['144'])).
% 0.91/1.14  
% 0.91/1.14  % SZS output end Refutation
% 0.91/1.14  
% 0.98/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
