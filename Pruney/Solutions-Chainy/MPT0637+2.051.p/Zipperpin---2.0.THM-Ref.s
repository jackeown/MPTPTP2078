%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R1kxcTDfcT

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:03 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 223 expanded)
%              Number of leaves         :   33 (  86 expanded)
%              Depth                    :   20
%              Number of atoms          : 1154 (1773 expanded)
%              Number of equality atoms :   81 ( 142 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k8_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
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

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t127_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X36 @ ( k8_relat_1 @ X37 @ X38 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X36 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X36 @ ( k8_relat_1 @ X37 @ X38 ) )
        = ( k8_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) ) @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X36 @ ( k8_relat_1 @ X37 @ X38 ) )
        = ( k8_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) ) @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k8_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) @ X3 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('26',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('27',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X48 ) @ X49 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X49 ) @ X48 )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','37'])).

thf('39',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k8_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('42',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X47 ) @ X46 ) @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k8_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('48',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X46 @ ( k6_relat_1 @ X47 ) ) @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('51',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('55',plain,(
    ! [X35: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X35 ) @ X35 )
        = X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X36 @ ( k8_relat_1 @ X37 @ X38 ) )
        = ( k8_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) ) @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('60',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k8_relat_1 @ X34 @ X33 )
        = ( k3_xboole_0 @ X33 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('61',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('62',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k8_relat_1 @ X34 @ X33 )
        = ( k1_setfam_1 @ ( k2_tarski @ X33 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ X34 ) ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('64',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('65',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','73'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( r1_tarski @ ( k2_relat_1 @ X40 ) @ ( k2_relat_1 @ X39 ) )
      | ~ ( r1_tarski @ X40 @ X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('78',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('79',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('80',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('83',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k8_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('84',plain,(
    ! [X45: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X45 ) )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('85',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X42 @ X41 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X41 ) @ ( k4_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X45: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X45 ) )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('91',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('92',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','93'])).

thf('95',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k8_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ X31 @ ( k6_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('104',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
 != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','105'])).

thf('107',plain,(
    $false ),
    inference(simplify,[status(thm)],['106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R1kxcTDfcT
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:55:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 745 iterations in 0.483s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.75/0.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.94  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.75/0.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.94  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.94  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.75/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.75/0.94  thf(t123_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ B ) =>
% 0.75/0.94       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.75/0.94  thf('0', plain,
% 0.75/0.94      (![X31 : $i, X32 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X32 @ X31) = (k5_relat_1 @ X31 @ (k6_relat_1 @ X32)))
% 0.75/0.94          | ~ (v1_relat_1 @ X31))),
% 0.75/0.94      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.75/0.94  thf(t43_funct_1, conjecture,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.75/0.94       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.94    (~( ![A:$i,B:$i]:
% 0.75/0.94        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.75/0.94          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.75/0.94  thf('1', plain,
% 0.75/0.94      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.75/0.94         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(t12_setfam_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.94  thf('2', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i]:
% 0.75/0.94         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.94  thf('3', plain,
% 0.75/0.94      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.75/0.94         != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['1', '2'])).
% 0.75/0.94  thf('4', plain,
% 0.75/0.94      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.75/0.94          != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))
% 0.75/0.94        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['0', '3'])).
% 0.75/0.94  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.75/0.94  thf('5', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.94  thf('6', plain,
% 0.75/0.94      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.75/0.94         != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['4', '5'])).
% 0.75/0.94  thf(t127_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ C ) =>
% 0.75/0.94       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.75/0.94         ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X36 @ (k8_relat_1 @ X37 @ X38))
% 0.75/0.94            = (k8_relat_1 @ (k3_xboole_0 @ X36 @ X37) @ X38))
% 0.75/0.94          | ~ (v1_relat_1 @ X38))),
% 0.75/0.94      inference('cnf', [status(esa)], [t127_relat_1])).
% 0.75/0.94  thf('8', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i]:
% 0.75/0.94         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.94  thf('9', plain,
% 0.75/0.94      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X36 @ (k8_relat_1 @ X37 @ X38))
% 0.75/0.94            = (k8_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X36 @ X37)) @ X38))
% 0.75/0.94          | ~ (v1_relat_1 @ X38))),
% 0.75/0.94      inference('demod', [status(thm)], ['7', '8'])).
% 0.75/0.94  thf('10', plain,
% 0.75/0.94      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X36 @ (k8_relat_1 @ X37 @ X38))
% 0.75/0.94            = (k8_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X36 @ X37)) @ X38))
% 0.75/0.94          | ~ (v1_relat_1 @ X38))),
% 0.75/0.94      inference('demod', [status(thm)], ['7', '8'])).
% 0.75/0.94  thf(t48_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.94  thf('11', plain,
% 0.75/0.94      (![X10 : $i, X11 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.75/0.94           = (k3_xboole_0 @ X10 @ X11))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('12', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i]:
% 0.75/0.94         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.94  thf('13', plain,
% 0.75/0.94      (![X10 : $i, X11 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.75/0.94           = (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))),
% 0.75/0.94      inference('demod', [status(thm)], ['11', '12'])).
% 0.75/0.94  thf('14', plain,
% 0.75/0.94      (![X31 : $i, X32 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X32 @ X31) = (k5_relat_1 @ X31 @ (k6_relat_1 @ X32)))
% 0.75/0.94          | ~ (v1_relat_1 @ X31))),
% 0.75/0.94      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      (![X10 : $i, X11 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.75/0.94           = (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))),
% 0.75/0.94      inference('demod', [status(thm)], ['11', '12'])).
% 0.75/0.94  thf('16', plain,
% 0.75/0.94      (![X10 : $i, X11 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.75/0.94           = (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))),
% 0.75/0.94      inference('demod', [status(thm)], ['11', '12'])).
% 0.75/0.94  thf('17', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.75/0.94           = (k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['15', '16'])).
% 0.75/0.94  thf(t47_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.75/0.94  thf('18', plain,
% 0.75/0.94      (![X8 : $i, X9 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.75/0.94           = (k4_xboole_0 @ X8 @ X9))),
% 0.75/0.94      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.75/0.94  thf('19', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i]:
% 0.75/0.94         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.94  thf('20', plain,
% 0.75/0.94      (![X8 : $i, X9 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X8 @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)))
% 0.75/0.94           = (k4_xboole_0 @ X8 @ X9))),
% 0.75/0.94      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X1 @ X0)
% 0.75/0.94           = (k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.75/0.94      inference('demod', [status(thm)], ['17', '20'])).
% 0.75/0.94  thf(t17_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.75/0.94  thf('22', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.75/0.94      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.94  thf('23', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i]:
% 0.75/0.94         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.94  thf('24', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i]:
% 0.75/0.94         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 0.75/0.94      inference('demod', [status(thm)], ['22', '23'])).
% 0.75/0.94  thf('25', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.75/0.94      inference('sup+', [status(thm)], ['21', '24'])).
% 0.75/0.94  thf(t71_relat_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.75/0.94       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.75/0.94  thf('26', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.75/0.94      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.94  thf(t77_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ B ) =>
% 0.75/0.94       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.75/0.94         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.75/0.94  thf('27', plain,
% 0.75/0.94      (![X48 : $i, X49 : $i]:
% 0.75/0.94         (~ (r1_tarski @ (k1_relat_1 @ X48) @ X49)
% 0.75/0.94          | ((k5_relat_1 @ (k6_relat_1 @ X49) @ X48) = (X48))
% 0.75/0.94          | ~ (v1_relat_1 @ X48))),
% 0.75/0.94      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X0 @ X1)
% 0.75/0.94          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.75/0.94          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.75/0.94              = (k6_relat_1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['26', '27'])).
% 0.75/0.94  thf('29', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X0 @ X1)
% 0.75/0.94          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.75/0.94              = (k6_relat_1 @ X0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['28', '29'])).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.75/0.94           (k6_relat_1 @ (k4_xboole_0 @ X0 @ X1)))
% 0.75/0.94           = (k6_relat_1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['25', '30'])).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((k8_relat_1 @ (k4_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.75/0.94            = (k6_relat_1 @ (k4_xboole_0 @ X0 @ X1)))
% 0.75/0.94          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['14', '31'])).
% 0.75/0.94  thf('33', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k8_relat_1 @ (k4_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.75/0.94           = (k6_relat_1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k8_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.75/0.94           (k6_relat_1 @ X1))
% 0.75/0.94           = (k6_relat_1 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['13', '34'])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      (![X10 : $i, X11 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.75/0.94           = (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))),
% 0.75/0.94      inference('demod', [status(thm)], ['11', '12'])).
% 0.75/0.94  thf('37', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k8_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.75/0.94           (k6_relat_1 @ X1))
% 0.75/0.94           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.75/0.94      inference('demod', [status(thm)], ['35', '36'])).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.75/0.94            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))
% 0.75/0.94          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['10', '37'])).
% 0.75/0.94  thf('39', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.75/0.94           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.75/0.94      inference('demod', [status(thm)], ['38', '39'])).
% 0.75/0.94  thf('41', plain,
% 0.75/0.94      (![X31 : $i, X32 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X32 @ X31) = (k5_relat_1 @ X31 @ (k6_relat_1 @ X32)))
% 0.75/0.94          | ~ (v1_relat_1 @ X31))),
% 0.75/0.94      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.75/0.94  thf(t76_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ B ) =>
% 0.75/0.94       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.75/0.94         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (![X46 : $i, X47 : $i]:
% 0.75/0.94         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X47) @ X46) @ X46)
% 0.75/0.94          | ~ (v1_relat_1 @ X46))),
% 0.75/0.94      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.75/0.94           (k6_relat_1 @ X1))
% 0.75/0.94          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['41', '42'])).
% 0.75/0.94  thf('44', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.94  thf('45', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.94  thf('46', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X1))),
% 0.75/0.94      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      (![X31 : $i, X32 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X32 @ X31) = (k5_relat_1 @ X31 @ (k6_relat_1 @ X32)))
% 0.75/0.94          | ~ (v1_relat_1 @ X31))),
% 0.75/0.94      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.75/0.94  thf('48', plain,
% 0.75/0.94      (![X46 : $i, X47 : $i]:
% 0.75/0.94         ((r1_tarski @ (k5_relat_1 @ X46 @ (k6_relat_1 @ X47)) @ X46)
% 0.75/0.94          | ~ (v1_relat_1 @ X46))),
% 0.75/0.94      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['47', '48'])).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['49'])).
% 0.75/0.94  thf(t1_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.75/0.94       ( r1_tarski @ A @ C ) ))).
% 0.75/0.94  thf('51', plain,
% 0.75/0.94      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X5 @ X6)
% 0.75/0.94          | ~ (r1_tarski @ X6 @ X7)
% 0.75/0.94          | (r1_tarski @ X5 @ X7))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.75/0.94  thf('52', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0)
% 0.75/0.94          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.75/0.94          | ~ (r1_tarski @ X0 @ X2))),
% 0.75/0.94      inference('sup-', [status(thm)], ['50', '51'])).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((r1_tarski @ 
% 0.75/0.94           (k8_relat_1 @ X2 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.75/0.94           (k6_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['46', '52'])).
% 0.75/0.94  thf('54', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.75/0.94      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.94  thf(t126_relat_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ A ) =>
% 0.75/0.94       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.75/0.94  thf('55', plain,
% 0.75/0.94      (![X35 : $i]:
% 0.75/0.94         (((k8_relat_1 @ (k2_relat_1 @ X35) @ X35) = (X35))
% 0.75/0.94          | ~ (v1_relat_1 @ X35))),
% 0.75/0.94      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.75/0.94  thf('56', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['54', '55'])).
% 0.75/0.94  thf('57', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.94  thf('58', plain,
% 0.75/0.94      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['56', '57'])).
% 0.75/0.94  thf('59', plain,
% 0.75/0.94      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X36 @ (k8_relat_1 @ X37 @ X38))
% 0.75/0.94            = (k8_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X36 @ X37)) @ X38))
% 0.75/0.94          | ~ (v1_relat_1 @ X38))),
% 0.75/0.94      inference('demod', [status(thm)], ['7', '8'])).
% 0.75/0.94  thf(t124_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ B ) =>
% 0.75/0.94       ( ( k8_relat_1 @ A @ B ) =
% 0.75/0.94         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.75/0.94  thf('60', plain,
% 0.75/0.94      (![X33 : $i, X34 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X34 @ X33)
% 0.75/0.94            = (k3_xboole_0 @ X33 @ (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ X34)))
% 0.75/0.94          | ~ (v1_relat_1 @ X33))),
% 0.75/0.94      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.75/0.94  thf('61', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i]:
% 0.75/0.94         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.94  thf('62', plain,
% 0.75/0.94      (![X33 : $i, X34 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X34 @ X33)
% 0.75/0.94            = (k1_setfam_1 @ 
% 0.75/0.94               (k2_tarski @ X33 @ (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ X34))))
% 0.75/0.94          | ~ (v1_relat_1 @ X33))),
% 0.75/0.94      inference('demod', [status(thm)], ['60', '61'])).
% 0.75/0.94  thf(fc1_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.94  thf('63', plain,
% 0.75/0.94      (![X29 : $i, X30 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X29) | (v1_relat_1 @ (k3_xboole_0 @ X29 @ X30)))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.75/0.94  thf('64', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i]:
% 0.75/0.94         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.94  thf('65', plain,
% 0.75/0.94      (![X29 : $i, X30 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X29)
% 0.75/0.94          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X29 @ X30))))),
% 0.75/0.94      inference('demod', [status(thm)], ['63', '64'])).
% 0.75/0.94  thf('66', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.75/0.94          | ~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['62', '65'])).
% 0.75/0.94  thf('67', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['66'])).
% 0.75/0.94  thf('68', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((v1_relat_1 @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)))
% 0.75/0.94          | ~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['59', '67'])).
% 0.75/0.94  thf('69', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0)
% 0.75/0.94          | (v1_relat_1 @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['68'])).
% 0.75/0.94  thf('70', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.75/0.94          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['58', '69'])).
% 0.75/0.94  thf('71', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.94  thf('72', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['70', '71'])).
% 0.75/0.94  thf('73', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (r1_tarski @ 
% 0.75/0.94          (k8_relat_1 @ X2 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.75/0.94          (k6_relat_1 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['53', '72'])).
% 0.75/0.94  thf('74', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (r1_tarski @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.75/0.94          (k6_relat_1 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['40', '73'])).
% 0.75/0.94  thf(t25_relat_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ A ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( v1_relat_1 @ B ) =>
% 0.75/0.94           ( ( r1_tarski @ A @ B ) =>
% 0.75/0.94             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.75/0.94               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.75/0.94  thf('75', plain,
% 0.75/0.94      (![X39 : $i, X40 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X39)
% 0.75/0.94          | (r1_tarski @ (k2_relat_1 @ X40) @ (k2_relat_1 @ X39))
% 0.75/0.94          | ~ (r1_tarski @ X40 @ X39)
% 0.75/0.94          | ~ (v1_relat_1 @ X40))),
% 0.75/0.94      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.75/0.94  thf('76', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.75/0.94          | (r1_tarski @ 
% 0.75/0.94             (k2_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))) @ 
% 0.75/0.94             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.75/0.94          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['74', '75'])).
% 0.75/0.94  thf('77', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.94  thf('78', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.75/0.94      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.94  thf('79', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.75/0.94      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.94  thf('80', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.94  thf('81', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.75/0.94      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.75/0.94  thf('82', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X0 @ X1)
% 0.75/0.94          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.75/0.94              = (k6_relat_1 @ X0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['28', '29'])).
% 0.75/0.94  thf('83', plain,
% 0.75/0.94      (![X31 : $i, X32 : $i]:
% 0.75/0.94         (((k8_relat_1 @ X32 @ X31) = (k5_relat_1 @ X31 @ (k6_relat_1 @ X32)))
% 0.75/0.94          | ~ (v1_relat_1 @ X31))),
% 0.75/0.94      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.75/0.94  thf(t72_relat_1, axiom,
% 0.75/0.94    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.75/0.94  thf('84', plain,
% 0.75/0.94      (![X45 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X45)) = (k6_relat_1 @ X45))),
% 0.75/0.94      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.75/0.94  thf(t54_relat_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ A ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( v1_relat_1 @ B ) =>
% 0.75/0.94           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.75/0.94             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.75/0.94  thf('85', plain,
% 0.75/0.94      (![X41 : $i, X42 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X41)
% 0.75/0.94          | ((k4_relat_1 @ (k5_relat_1 @ X42 @ X41))
% 0.75/0.94              = (k5_relat_1 @ (k4_relat_1 @ X41) @ (k4_relat_1 @ X42)))
% 0.75/0.94          | ~ (v1_relat_1 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.75/0.94  thf('86', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.75/0.94            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.75/0.94          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_relat_1 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['84', '85'])).
% 0.75/0.94  thf('87', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.95  thf('88', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.75/0.95            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.75/0.95          | ~ (v1_relat_1 @ X1))),
% 0.75/0.95      inference('demod', [status(thm)], ['86', '87'])).
% 0.75/0.95  thf('89', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.75/0.95            = (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X1)) @ 
% 0.75/0.95               (k6_relat_1 @ X0)))
% 0.75/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.75/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.95      inference('sup+', [status(thm)], ['83', '88'])).
% 0.75/0.95  thf('90', plain,
% 0.75/0.95      (![X45 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X45)) = (k6_relat_1 @ X45))),
% 0.75/0.95      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.75/0.95  thf('91', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.95  thf('92', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.95  thf('93', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.75/0.95           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.75/0.95  thf('94', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (r1_tarski @ X0 @ X1)
% 0.75/0.95          | ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.75/0.95              = (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['82', '93'])).
% 0.75/0.95  thf('95', plain,
% 0.75/0.95      (![X31 : $i, X32 : $i]:
% 0.75/0.95         (((k8_relat_1 @ X32 @ X31) = (k5_relat_1 @ X31 @ (k6_relat_1 @ X32)))
% 0.75/0.95          | ~ (v1_relat_1 @ X31))),
% 0.75/0.95      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.75/0.95  thf('96', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.75/0.95           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.75/0.95  thf('97', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.75/0.95            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.75/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('sup+', [status(thm)], ['95', '96'])).
% 0.75/0.95  thf('98', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.95  thf('99', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.75/0.95           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['97', '98'])).
% 0.75/0.95  thf('100', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (r1_tarski @ X0 @ X1)
% 0.75/0.95          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['94', '99'])).
% 0.75/0.95  thf('101', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((k8_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.75/0.95           (k6_relat_1 @ X0))
% 0.75/0.95           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['81', '100'])).
% 0.75/0.95  thf('102', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X0)))
% 0.75/0.95            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.75/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('sup+', [status(thm)], ['9', '101'])).
% 0.75/0.95  thf('103', plain,
% 0.75/0.95      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.75/0.95      inference('demod', [status(thm)], ['56', '57'])).
% 0.75/0.95  thf('104', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.95  thf('105', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.75/0.95           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.75/0.95      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.75/0.95  thf('106', plain,
% 0.75/0.95      (((k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.75/0.95         != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.75/0.95      inference('demod', [status(thm)], ['6', '105'])).
% 0.75/0.95  thf('107', plain, ($false), inference('simplify', [status(thm)], ['106'])).
% 0.75/0.95  
% 0.75/0.95  % SZS output end Refutation
% 0.75/0.95  
% 0.79/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
