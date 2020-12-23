%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0oYpdgnTiV

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:07 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  204 (9336 expanded)
%              Number of leaves         :   28 (3420 expanded)
%              Depth                    :   23
%              Number of atoms          : 1892 (77262 expanded)
%              Number of equality atoms :  131 (5350 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('7',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X35 ) @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k8_relat_1 @ X24 @ X23 )
        = ( k3_xboole_0 @ X23 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X23 ) @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) @ X1 ) ),
    inference(demod,[status(thm)],['11','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','24'])).

thf('26',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('28',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ( ( k7_relat_1 @ X40 @ X41 )
        = X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k7_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('32',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k7_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) @ X17 )
        = ( k7_relat_1 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('40',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30','41'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('43',plain,(
    ! [X34: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('44',plain,(
    ! [X34: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X28 @ X27 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X27 ) @ ( k4_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k7_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('52',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('53',plain,(
    ! [X37: $i] :
      ( ( ( k5_relat_1 @ X37 @ ( k6_relat_1 @ ( k2_relat_1 @ X37 ) ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k5_relat_1 @ X30 @ ( k5_relat_1 @ X29 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('60',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','61'])).

thf('63',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['50','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('68',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('69',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k7_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('70',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('71',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('77',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('78',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('79',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','80'])).

thf('82',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ( ( k7_relat_1 @ X40 @ X41 )
        = X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','88','89'])).

thf('92',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','90','91','92'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('98',plain,(
    ! [X37: $i] :
      ( ( ( k5_relat_1 @ X37 @ ( k6_relat_1 @ ( k2_relat_1 @ X37 ) ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('99',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k7_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('102',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('103',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('104',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) @ X17 )
        = ( k7_relat_1 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X37: $i] :
      ( ( ( k5_relat_1 @ X37 @ ( k6_relat_1 @ ( k2_relat_1 @ X37 ) ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('114',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('115',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k5_relat_1 @ X30 @ ( k5_relat_1 @ X29 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['113','119'])).

thf('121',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('122',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('123',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('124',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['112','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','88','89'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('129',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['97','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k7_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','88','89'])).

thf('139',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('140',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k5_relat_1 @ X30 @ ( k5_relat_1 @ X29 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['138','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('146',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('147',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','88','89'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','88','89'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['144','145','146','147','148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['137','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','90','91','92'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['136','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','90','91','92'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('160',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['157','158','163'])).

thf('165',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['157','158','163'])).

thf('167',plain,(
    ! [X34: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['157','158','163'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','90','91','92'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['165','172'])).

thf('174',plain,(
    $false ),
    inference(simplify,[status(thm)],['173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0oYpdgnTiV
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.81  % Solved by: fo/fo7.sh
% 0.53/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.81  % done 563 iterations in 0.352s
% 0.53/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.81  % SZS output start Refutation
% 0.53/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.81  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.53/0.81  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.53/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.81  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.53/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.53/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.81  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.53/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.81  thf(t123_relat_1, axiom,
% 0.53/0.81    (![A:$i,B:$i]:
% 0.53/0.81     ( ( v1_relat_1 @ B ) =>
% 0.53/0.81       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.53/0.81  thf('0', plain,
% 0.53/0.81      (![X21 : $i, X22 : $i]:
% 0.53/0.81         (((k8_relat_1 @ X22 @ X21) = (k5_relat_1 @ X21 @ (k6_relat_1 @ X22)))
% 0.53/0.81          | ~ (v1_relat_1 @ X21))),
% 0.53/0.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.81  thf(t43_funct_1, conjecture,
% 0.53/0.81    (![A:$i,B:$i]:
% 0.53/0.81     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.53/0.81       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.81    (~( ![A:$i,B:$i]:
% 0.53/0.81        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.53/0.81          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.53/0.81    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.53/0.81  thf('1', plain,
% 0.53/0.81      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.53/0.81         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.81  thf('2', plain,
% 0.53/0.81      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.53/0.81          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.53/0.81        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.53/0.81      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.81  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.53/0.81  thf('3', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.81  thf('4', plain,
% 0.53/0.81      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.53/0.81         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.81      inference('demod', [status(thm)], ['2', '3'])).
% 0.53/0.81  thf('5', plain,
% 0.53/0.81      (![X21 : $i, X22 : $i]:
% 0.53/0.81         (((k8_relat_1 @ X22 @ X21) = (k5_relat_1 @ X21 @ (k6_relat_1 @ X22)))
% 0.53/0.81          | ~ (v1_relat_1 @ X21))),
% 0.53/0.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.81  thf('6', plain,
% 0.53/0.81      (![X21 : $i, X22 : $i]:
% 0.53/0.81         (((k8_relat_1 @ X22 @ X21) = (k5_relat_1 @ X21 @ (k6_relat_1 @ X22)))
% 0.53/0.81          | ~ (v1_relat_1 @ X21))),
% 0.53/0.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.81  thf(t76_relat_1, axiom,
% 0.53/0.81    (![A:$i,B:$i]:
% 0.53/0.81     ( ( v1_relat_1 @ B ) =>
% 0.53/0.81       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.53/0.81         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.53/0.81  thf('7', plain,
% 0.53/0.81      (![X35 : $i, X36 : $i]:
% 0.53/0.81         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X36) @ X35) @ X35)
% 0.53/0.81          | ~ (v1_relat_1 @ X35))),
% 0.53/0.81      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.53/0.81  thf(t25_relat_1, axiom,
% 0.53/0.81    (![A:$i]:
% 0.53/0.81     ( ( v1_relat_1 @ A ) =>
% 0.53/0.81       ( ![B:$i]:
% 0.53/0.81         ( ( v1_relat_1 @ B ) =>
% 0.53/0.81           ( ( r1_tarski @ A @ B ) =>
% 0.53/0.81             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.53/0.81               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.53/0.81  thf('8', plain,
% 0.53/0.81      (![X25 : $i, X26 : $i]:
% 0.53/0.81         (~ (v1_relat_1 @ X25)
% 0.53/0.81          | (r1_tarski @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25))
% 0.53/0.81          | ~ (r1_tarski @ X26 @ X25)
% 0.53/0.81          | ~ (v1_relat_1 @ X26))),
% 0.53/0.81      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.53/0.81  thf('9', plain,
% 0.53/0.81      (![X0 : $i, X1 : $i]:
% 0.53/0.81         (~ (v1_relat_1 @ X0)
% 0.53/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.81          | (r1_tarski @ 
% 0.53/0.81             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.53/0.81             (k1_relat_1 @ X0))
% 0.53/0.81          | ~ (v1_relat_1 @ X0))),
% 0.53/0.81      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.81  thf('10', plain,
% 0.53/0.81      (![X0 : $i, X1 : $i]:
% 0.53/0.81         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.53/0.81           (k1_relat_1 @ X0))
% 0.53/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.81          | ~ (v1_relat_1 @ X0))),
% 0.53/0.81      inference('simplify', [status(thm)], ['9'])).
% 0.53/0.81  thf('11', plain,
% 0.53/0.81      (![X0 : $i, X1 : $i]:
% 0.53/0.81         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.53/0.81          | (r1_tarski @ 
% 0.53/0.81             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))) @ 
% 0.53/0.81             (k1_relat_1 @ (k6_relat_1 @ X1))))),
% 0.53/0.81      inference('sup-', [status(thm)], ['6', '10'])).
% 0.53/0.81  thf(t71_relat_1, axiom,
% 0.53/0.81    (![A:$i]:
% 0.53/0.81     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.53/0.81       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.53/0.81  thf('12', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 0.53/0.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.81  thf(t124_relat_1, axiom,
% 0.53/0.81    (![A:$i,B:$i]:
% 0.53/0.81     ( ( v1_relat_1 @ B ) =>
% 0.53/0.81       ( ( k8_relat_1 @ A @ B ) =
% 0.53/0.81         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.53/0.81  thf('13', plain,
% 0.53/0.81      (![X23 : $i, X24 : $i]:
% 0.53/0.81         (((k8_relat_1 @ X24 @ X23)
% 0.53/0.81            = (k3_xboole_0 @ X23 @ (k2_zfmisc_1 @ (k1_relat_1 @ X23) @ X24)))
% 0.53/0.81          | ~ (v1_relat_1 @ X23))),
% 0.53/0.81      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.53/0.81  thf('14', plain,
% 0.53/0.81      (![X0 : $i, X1 : $i]:
% 0.53/0.81         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.53/0.81            = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.53/0.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.81      inference('sup+', [status(thm)], ['12', '13'])).
% 0.53/0.81  thf('15', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.81  thf('16', plain,
% 0.53/0.81      (![X0 : $i, X1 : $i]:
% 0.53/0.81         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.53/0.81           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.53/0.82      inference('demod', [status(thm)], ['14', '15'])).
% 0.53/0.82  thf(fc1_relat_1, axiom,
% 0.53/0.82    (![A:$i,B:$i]:
% 0.53/0.82     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.82  thf('17', plain,
% 0.53/0.82      (![X12 : $i, X13 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.53/0.82      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.53/0.82  thf('18', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['16', '17'])).
% 0.53/0.82  thf('19', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('20', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.82  thf('21', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('22', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('23', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 0.53/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.82  thf('24', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (r1_tarski @ 
% 0.53/0.82          (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))) @ 
% 0.53/0.82          X1)),
% 0.53/0.82      inference('demod', [status(thm)], ['11', '20', '21', '22', '23'])).
% 0.53/0.82  thf('25', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.53/0.82           X1)
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['5', '24'])).
% 0.53/0.82  thf('26', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('27', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1)),
% 0.53/0.82      inference('demod', [status(thm)], ['25', '26'])).
% 0.53/0.82  thf(t97_relat_1, axiom,
% 0.53/0.82    (![A:$i,B:$i]:
% 0.53/0.82     ( ( v1_relat_1 @ B ) =>
% 0.53/0.82       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.53/0.82         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.53/0.82  thf('28', plain,
% 0.53/0.82      (![X40 : $i, X41 : $i]:
% 0.53/0.82         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.53/0.82          | ((k7_relat_1 @ X40 @ X41) = (X40))
% 0.53/0.82          | ~ (v1_relat_1 @ X40))),
% 0.53/0.82      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.53/0.82  thf('29', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.82          | ((k7_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 0.53/0.82              = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.53/0.82      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.82  thf('30', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.82  thf('31', plain,
% 0.53/0.82      (![X21 : $i, X22 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X22 @ X21) = (k5_relat_1 @ X21 @ (k6_relat_1 @ X22)))
% 0.53/0.82          | ~ (v1_relat_1 @ X21))),
% 0.53/0.82      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.82  thf(t94_relat_1, axiom,
% 0.53/0.82    (![A:$i,B:$i]:
% 0.53/0.82     ( ( v1_relat_1 @ B ) =>
% 0.53/0.82       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.53/0.82  thf('32', plain,
% 0.53/0.82      (![X38 : $i, X39 : $i]:
% 0.53/0.82         (((k7_relat_1 @ X39 @ X38) = (k5_relat_1 @ (k6_relat_1 @ X38) @ X39))
% 0.53/0.82          | ~ (v1_relat_1 @ X39))),
% 0.53/0.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.82  thf('33', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.82            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['31', '32'])).
% 0.53/0.82  thf('34', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('35', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('36', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.53/0.82  thf(t100_relat_1, axiom,
% 0.53/0.82    (![A:$i,B:$i,C:$i]:
% 0.53/0.82     ( ( v1_relat_1 @ C ) =>
% 0.53/0.82       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.53/0.82         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.53/0.82  thf('37', plain,
% 0.53/0.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.53/0.82         (((k7_relat_1 @ (k7_relat_1 @ X15 @ X16) @ X17)
% 0.53/0.82            = (k7_relat_1 @ X15 @ (k3_xboole_0 @ X16 @ X17)))
% 0.53/0.82          | ~ (v1_relat_1 @ X15))),
% 0.53/0.82      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.53/0.82  thf('38', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.53/0.82            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['36', '37'])).
% 0.53/0.82  thf('39', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.53/0.82  thf('40', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('41', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.53/0.82      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.53/0.82  thf('42', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('demod', [status(thm)], ['29', '30', '41'])).
% 0.53/0.82  thf(t72_relat_1, axiom,
% 0.53/0.82    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.53/0.82  thf('43', plain,
% 0.53/0.82      (![X34 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X34)) = (k6_relat_1 @ X34))),
% 0.53/0.82      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.53/0.82  thf('44', plain,
% 0.53/0.82      (![X34 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X34)) = (k6_relat_1 @ X34))),
% 0.53/0.82      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.53/0.82  thf(t54_relat_1, axiom,
% 0.53/0.82    (![A:$i]:
% 0.53/0.82     ( ( v1_relat_1 @ A ) =>
% 0.53/0.82       ( ![B:$i]:
% 0.53/0.82         ( ( v1_relat_1 @ B ) =>
% 0.53/0.82           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.53/0.82             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.53/0.82  thf('45', plain,
% 0.53/0.82      (![X27 : $i, X28 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ X27)
% 0.53/0.82          | ((k4_relat_1 @ (k5_relat_1 @ X28 @ X27))
% 0.53/0.82              = (k5_relat_1 @ (k4_relat_1 @ X27) @ (k4_relat_1 @ X28)))
% 0.53/0.82          | ~ (v1_relat_1 @ X28))),
% 0.53/0.82      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.53/0.82  thf('46', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.53/0.82          | ~ (v1_relat_1 @ X1)
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['44', '45'])).
% 0.53/0.82  thf('47', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('48', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.53/0.82          | ~ (v1_relat_1 @ X1))),
% 0.53/0.82      inference('demod', [status(thm)], ['46', '47'])).
% 0.53/0.82  thf('49', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.53/0.82            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['43', '48'])).
% 0.53/0.82  thf('50', plain,
% 0.53/0.82      (![X38 : $i, X39 : $i]:
% 0.53/0.82         (((k7_relat_1 @ X39 @ X38) = (k5_relat_1 @ (k6_relat_1 @ X38) @ X39))
% 0.53/0.82          | ~ (v1_relat_1 @ X39))),
% 0.53/0.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.82  thf('51', plain,
% 0.53/0.82      (![X21 : $i, X22 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X22 @ X21) = (k5_relat_1 @ X21 @ (k6_relat_1 @ X22)))
% 0.53/0.82          | ~ (v1_relat_1 @ X21))),
% 0.53/0.82      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.82  thf('52', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 0.53/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.82  thf(t80_relat_1, axiom,
% 0.53/0.82    (![A:$i]:
% 0.53/0.82     ( ( v1_relat_1 @ A ) =>
% 0.53/0.82       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.53/0.82  thf('53', plain,
% 0.53/0.82      (![X37 : $i]:
% 0.53/0.82         (((k5_relat_1 @ X37 @ (k6_relat_1 @ (k2_relat_1 @ X37))) = (X37))
% 0.53/0.82          | ~ (v1_relat_1 @ X37))),
% 0.53/0.82      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.53/0.82  thf('54', plain,
% 0.53/0.82      (![X0 : $i]:
% 0.53/0.82         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.53/0.82            = (k6_relat_1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['52', '53'])).
% 0.53/0.82  thf('55', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('56', plain,
% 0.53/0.82      (![X0 : $i]:
% 0.53/0.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.53/0.82           = (k6_relat_1 @ X0))),
% 0.53/0.82      inference('demod', [status(thm)], ['54', '55'])).
% 0.53/0.82  thf(t55_relat_1, axiom,
% 0.53/0.82    (![A:$i]:
% 0.53/0.82     ( ( v1_relat_1 @ A ) =>
% 0.53/0.82       ( ![B:$i]:
% 0.53/0.82         ( ( v1_relat_1 @ B ) =>
% 0.53/0.82           ( ![C:$i]:
% 0.53/0.82             ( ( v1_relat_1 @ C ) =>
% 0.53/0.82               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.53/0.82                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.53/0.82  thf('57', plain,
% 0.53/0.82      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ X29)
% 0.53/0.82          | ((k5_relat_1 @ (k5_relat_1 @ X30 @ X29) @ X31)
% 0.53/0.82              = (k5_relat_1 @ X30 @ (k5_relat_1 @ X29 @ X31)))
% 0.53/0.82          | ~ (v1_relat_1 @ X31)
% 0.53/0.82          | ~ (v1_relat_1 @ X30))),
% 0.53/0.82      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.53/0.82  thf('58', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.82            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.82               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ X1)
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['56', '57'])).
% 0.53/0.82  thf('59', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('60', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('61', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.82            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.82               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.53/0.82          | ~ (v1_relat_1 @ X1))),
% 0.53/0.82      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.53/0.82  thf('62', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.53/0.82            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.82               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['51', '61'])).
% 0.53/0.82  thf('63', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('64', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('65', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.82              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.53/0.82      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.53/0.82  thf('66', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.53/0.82            = (k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.53/0.82      inference('sup+', [status(thm)], ['50', '65'])).
% 0.53/0.82  thf('67', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.53/0.82      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.53/0.82  thf('68', plain,
% 0.53/0.82      (![X21 : $i, X22 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X22 @ X21) = (k5_relat_1 @ X21 @ (k6_relat_1 @ X22)))
% 0.53/0.82          | ~ (v1_relat_1 @ X21))),
% 0.53/0.82      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.82  thf('69', plain,
% 0.53/0.82      (![X38 : $i, X39 : $i]:
% 0.53/0.82         (((k7_relat_1 @ X39 @ X38) = (k5_relat_1 @ (k6_relat_1 @ X38) @ X39))
% 0.53/0.82          | ~ (v1_relat_1 @ X39))),
% 0.53/0.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.82  thf('70', plain,
% 0.53/0.82      (![X35 : $i, X36 : $i]:
% 0.53/0.82         ((r1_tarski @ (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)) @ X35)
% 0.53/0.82          | ~ (v1_relat_1 @ X35))),
% 0.53/0.82      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.53/0.82  thf('71', plain,
% 0.53/0.82      (![X25 : $i, X26 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ X25)
% 0.53/0.82          | (r1_tarski @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25))
% 0.53/0.82          | ~ (r1_tarski @ X26 @ X25)
% 0.53/0.82          | ~ (v1_relat_1 @ X26))),
% 0.53/0.82      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.53/0.82  thf('72', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ X0)
% 0.53/0.82          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.82          | (r1_tarski @ 
% 0.53/0.82             (k1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.53/0.82             (k1_relat_1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ X0))),
% 0.53/0.82      inference('sup-', [status(thm)], ['70', '71'])).
% 0.53/0.82  thf('73', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.53/0.82           (k1_relat_1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.82          | ~ (v1_relat_1 @ X0))),
% 0.53/0.82      inference('simplify', [status(thm)], ['72'])).
% 0.53/0.82  thf('74', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.82          | (r1_tarski @ 
% 0.53/0.82             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))) @ 
% 0.53/0.82             (k1_relat_1 @ (k6_relat_1 @ X0))))),
% 0.53/0.82      inference('sup-', [status(thm)], ['69', '73'])).
% 0.53/0.82  thf('75', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.53/0.82  thf('76', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.82  thf('77', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('78', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('79', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 0.53/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.82  thf('80', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (r1_tarski @ 
% 0.53/0.82          (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))) @ 
% 0.53/0.82          X0)),
% 0.53/0.82      inference('demod', [status(thm)], ['74', '75', '76', '77', '78', '79'])).
% 0.53/0.82  thf('81', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.53/0.82           X0)
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['68', '80'])).
% 0.53/0.82  thf('82', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('83', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)),
% 0.53/0.82      inference('demod', [status(thm)], ['81', '82'])).
% 0.53/0.82  thf('84', plain,
% 0.53/0.82      (![X40 : $i, X41 : $i]:
% 0.53/0.82         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.53/0.82          | ((k7_relat_1 @ X40 @ X41) = (X40))
% 0.53/0.82          | ~ (v1_relat_1 @ X40))),
% 0.53/0.82      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.53/0.82  thf('85', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82          | ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 0.53/0.82              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.53/0.82      inference('sup-', [status(thm)], ['83', '84'])).
% 0.53/0.82  thf('86', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.82  thf('87', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.53/0.82      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.53/0.82  thf('88', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.53/0.82  thf('89', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.82  thf('90', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['66', '67', '88', '89'])).
% 0.53/0.82  thf('91', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['66', '67', '88', '89'])).
% 0.53/0.82  thf('92', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('93', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('demod', [status(thm)], ['49', '90', '91', '92'])).
% 0.53/0.82  thf('94', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['42', '93'])).
% 0.53/0.82  thf('95', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('demod', [status(thm)], ['49', '90', '91', '92'])).
% 0.53/0.82  thf('96', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('demod', [status(thm)], ['94', '95'])).
% 0.53/0.82  thf('97', plain,
% 0.53/0.82      (![X21 : $i, X22 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X22 @ X21) = (k5_relat_1 @ X21 @ (k6_relat_1 @ X22)))
% 0.53/0.82          | ~ (v1_relat_1 @ X21))),
% 0.53/0.82      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.82  thf('98', plain,
% 0.53/0.82      (![X37 : $i]:
% 0.53/0.82         (((k5_relat_1 @ X37 @ (k6_relat_1 @ (k2_relat_1 @ X37))) = (X37))
% 0.53/0.82          | ~ (v1_relat_1 @ X37))),
% 0.53/0.82      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.53/0.82  thf('99', plain,
% 0.53/0.82      (![X38 : $i, X39 : $i]:
% 0.53/0.82         (((k7_relat_1 @ X39 @ X38) = (k5_relat_1 @ (k6_relat_1 @ X38) @ X39))
% 0.53/0.82          | ~ (v1_relat_1 @ X39))),
% 0.53/0.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.82  thf('100', plain,
% 0.53/0.82      (![X0 : $i]:
% 0.53/0.82         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 0.53/0.82            = (k6_relat_1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 0.53/0.82      inference('sup+', [status(thm)], ['98', '99'])).
% 0.53/0.82  thf('101', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 0.53/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.82  thf('102', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('103', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 0.53/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.82  thf('104', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('105', plain,
% 0.53/0.82      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.53/0.82      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 0.53/0.82  thf('106', plain,
% 0.53/0.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.53/0.82         (((k7_relat_1 @ (k7_relat_1 @ X15 @ X16) @ X17)
% 0.53/0.82            = (k7_relat_1 @ X15 @ (k3_xboole_0 @ X16 @ X17)))
% 0.53/0.82          | ~ (v1_relat_1 @ X15))),
% 0.53/0.82      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.53/0.82  thf('107', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.82            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['105', '106'])).
% 0.53/0.82  thf('108', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('109', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.82           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.53/0.82      inference('demod', [status(thm)], ['107', '108'])).
% 0.53/0.82  thf('110', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.53/0.82  thf('111', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.53/0.82  thf('112', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.53/0.82      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.53/0.82  thf('113', plain,
% 0.53/0.82      (![X37 : $i]:
% 0.53/0.82         (((k5_relat_1 @ X37 @ (k6_relat_1 @ (k2_relat_1 @ X37))) = (X37))
% 0.53/0.82          | ~ (v1_relat_1 @ X37))),
% 0.53/0.82      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.53/0.82  thf('114', plain,
% 0.53/0.82      (![X21 : $i, X22 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X22 @ X21) = (k5_relat_1 @ X21 @ (k6_relat_1 @ X22)))
% 0.53/0.82          | ~ (v1_relat_1 @ X21))),
% 0.53/0.82      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.82  thf('115', plain,
% 0.53/0.82      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ X29)
% 0.53/0.82          | ((k5_relat_1 @ (k5_relat_1 @ X30 @ X29) @ X31)
% 0.53/0.82              = (k5_relat_1 @ X30 @ (k5_relat_1 @ X29 @ X31)))
% 0.53/0.82          | ~ (v1_relat_1 @ X31)
% 0.53/0.82          | ~ (v1_relat_1 @ X30))),
% 0.53/0.82      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.53/0.82  thf('116', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         (((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.53/0.82            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 0.53/0.82          | ~ (v1_relat_1 @ X0)
% 0.53/0.82          | ~ (v1_relat_1 @ X0)
% 0.53/0.82          | ~ (v1_relat_1 @ X2)
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['114', '115'])).
% 0.53/0.82  thf('117', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('118', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         (((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.53/0.82            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 0.53/0.82          | ~ (v1_relat_1 @ X0)
% 0.53/0.82          | ~ (v1_relat_1 @ X0)
% 0.53/0.82          | ~ (v1_relat_1 @ X2))),
% 0.53/0.82      inference('demod', [status(thm)], ['116', '117'])).
% 0.53/0.82  thf('119', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ X2)
% 0.53/0.82          | ~ (v1_relat_1 @ X0)
% 0.53/0.82          | ((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.53/0.82              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2))))),
% 0.53/0.82      inference('simplify', [status(thm)], ['118'])).
% 0.53/0.82  thf('120', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k5_relat_1 @ (k8_relat_1 @ X0 @ X1) @ 
% 0.53/0.82            (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.53/0.82            = (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ X1)
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 0.53/0.82      inference('sup+', [status(thm)], ['113', '119'])).
% 0.53/0.82  thf('121', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 0.53/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.82  thf('122', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('123', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 0.53/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.82  thf('124', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('125', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k5_relat_1 @ (k8_relat_1 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.53/0.82            = (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82          | ~ (v1_relat_1 @ X1))),
% 0.53/0.82      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 0.53/0.82  thf('126', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.53/0.82            (k6_relat_1 @ X1))
% 0.53/0.82            = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.53/0.82               (k6_relat_1 @ X1)))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.53/0.82      inference('sup+', [status(thm)], ['112', '125'])).
% 0.53/0.82  thf('127', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['66', '67', '88', '89'])).
% 0.53/0.82  thf('128', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.53/0.82      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.53/0.82  thf('129', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('130', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.53/0.82           (k6_relat_1 @ X1)) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.53/0.82  thf('131', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.53/0.82      inference('sup+', [status(thm)], ['97', '130'])).
% 0.53/0.82  thf('132', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.82  thf('133', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['131', '132'])).
% 0.53/0.82  thf('134', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.53/0.82           (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['96', '133'])).
% 0.53/0.82  thf('135', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('demod', [status(thm)], ['94', '95'])).
% 0.53/0.82  thf('136', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.53/0.82           (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['134', '135'])).
% 0.53/0.82  thf('137', plain,
% 0.53/0.82      (![X38 : $i, X39 : $i]:
% 0.53/0.82         (((k7_relat_1 @ X39 @ X38) = (k5_relat_1 @ (k6_relat_1 @ X38) @ X39))
% 0.53/0.82          | ~ (v1_relat_1 @ X39))),
% 0.53/0.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.82  thf('138', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['66', '67', '88', '89'])).
% 0.53/0.82  thf('139', plain,
% 0.53/0.82      (![X21 : $i, X22 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X22 @ X21) = (k5_relat_1 @ X21 @ (k6_relat_1 @ X22)))
% 0.53/0.82          | ~ (v1_relat_1 @ X21))),
% 0.53/0.82      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.82  thf('140', plain,
% 0.53/0.82      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ X29)
% 0.53/0.82          | ((k5_relat_1 @ (k5_relat_1 @ X30 @ X29) @ X31)
% 0.53/0.82              = (k5_relat_1 @ X30 @ (k5_relat_1 @ X29 @ X31)))
% 0.53/0.82          | ~ (v1_relat_1 @ X31)
% 0.53/0.82          | ~ (v1_relat_1 @ X30))),
% 0.53/0.82      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.53/0.82  thf('141', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 0.53/0.82            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.53/0.82          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ X1)
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.53/0.82          | ~ (v1_relat_1 @ X0))),
% 0.53/0.82      inference('sup+', [status(thm)], ['139', '140'])).
% 0.53/0.82  thf('142', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('143', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 0.53/0.82            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.53/0.82          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ X1)
% 0.53/0.82          | ~ (v1_relat_1 @ X0))),
% 0.53/0.82      inference('demod', [status(thm)], ['141', '142'])).
% 0.53/0.82  thf('144', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.82          | ((k8_relat_1 @ X2 @ 
% 0.53/0.82              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.53/0.82              = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.82                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)))))),
% 0.53/0.82      inference('sup-', [status(thm)], ['138', '143'])).
% 0.53/0.82  thf('145', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.82  thf('146', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('147', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('148', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['66', '67', '88', '89'])).
% 0.53/0.82  thf('149', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['66', '67', '88', '89'])).
% 0.53/0.82  thf('150', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.82              (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 0.53/0.82      inference('demod', [status(thm)],
% 0.53/0.82                ['144', '145', '146', '147', '148', '149'])).
% 0.53/0.82  thf('151', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82            = (k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 0.53/0.82      inference('sup+', [status(thm)], ['137', '150'])).
% 0.53/0.82  thf('152', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.53/0.82      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.53/0.82  thf('153', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.82  thf('154', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.53/0.82      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.53/0.82  thf('155', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('demod', [status(thm)], ['49', '90', '91', '92'])).
% 0.53/0.82  thf('156', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.82         ((k4_relat_1 @ 
% 0.53/0.82           (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.53/0.82           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X2)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['154', '155'])).
% 0.53/0.82  thf('157', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.53/0.82              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.53/0.82      inference('sup+', [status(thm)], ['136', '156'])).
% 0.53/0.82  thf('158', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('demod', [status(thm)], ['49', '90', '91', '92'])).
% 0.53/0.82  thf('159', plain,
% 0.53/0.82      (![X0 : $i]:
% 0.53/0.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.53/0.82           = (k6_relat_1 @ X0))),
% 0.53/0.82      inference('demod', [status(thm)], ['54', '55'])).
% 0.53/0.82  thf('160', plain,
% 0.53/0.82      (![X21 : $i, X22 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X22 @ X21) = (k5_relat_1 @ X21 @ (k6_relat_1 @ X22)))
% 0.53/0.82          | ~ (v1_relat_1 @ X21))),
% 0.53/0.82      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.82  thf('161', plain,
% 0.53/0.82      (![X0 : $i]:
% 0.53/0.82         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.53/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['159', '160'])).
% 0.53/0.82  thf('162', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.53/0.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.82  thf('163', plain,
% 0.53/0.82      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.53/0.82      inference('demod', [status(thm)], ['161', '162'])).
% 0.53/0.82  thf('164', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['157', '158', '163'])).
% 0.53/0.82  thf('165', plain,
% 0.53/0.82      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.53/0.82         != (k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))),
% 0.53/0.82      inference('demod', [status(thm)], ['4', '164'])).
% 0.53/0.82  thf('166', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['157', '158', '163'])).
% 0.53/0.82  thf('167', plain,
% 0.53/0.82      (![X34 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X34)) = (k6_relat_1 @ X34))),
% 0.53/0.82      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.53/0.82  thf('168', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['166', '167'])).
% 0.53/0.82  thf('169', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.53/0.82           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['157', '158', '163'])).
% 0.53/0.82  thf('170', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.82      inference('demod', [status(thm)], ['168', '169'])).
% 0.53/0.82  thf('171', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.82           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('demod', [status(thm)], ['49', '90', '91', '92'])).
% 0.53/0.82  thf('172', plain,
% 0.53/0.82      (![X0 : $i, X1 : $i]:
% 0.53/0.82         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.53/0.82           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.53/0.82      inference('sup+', [status(thm)], ['170', '171'])).
% 0.53/0.82  thf('173', plain,
% 0.53/0.82      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.53/0.82         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.53/0.82      inference('demod', [status(thm)], ['165', '172'])).
% 0.53/0.82  thf('174', plain, ($false), inference('simplify', [status(thm)], ['173'])).
% 0.53/0.82  
% 0.53/0.82  % SZS output end Refutation
% 0.53/0.82  
% 0.65/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
