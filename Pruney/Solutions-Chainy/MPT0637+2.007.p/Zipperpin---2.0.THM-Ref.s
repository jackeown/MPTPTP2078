%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1hwXjNBib1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:56 EST 2020

% Result     : Theorem 6.80s
% Output     : Refutation 6.80s
% Verified   : 
% Statistics : Number of formulae       :  214 (3278 expanded)
%              Number of leaves         :   28 (1158 expanded)
%              Depth                    :   18
%              Number of atoms          : 2090 (28929 expanded)
%              Number of equality atoms :  148 (2462 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
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
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X29 ) @ X28 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('10',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X29 ) @ X28 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k5_relat_1 @ X22 @ ( k5_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X26 @ ( k6_relat_1 @ X27 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( X0
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X2 @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X2 @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('28',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X26 @ ( k6_relat_1 @ X27 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X26 @ ( k6_relat_1 @ X27 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X19 @ X20 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('59',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X19 @ X20 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['56','67'])).

thf('69',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X2 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['55','70'])).

thf('72',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('74',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X2 @ X1 ) ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['54','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('78',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X19 @ X20 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('86',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('89',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('90',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('91',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','79'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('95',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','79'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('100',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('101',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k5_relat_1 @ X22 @ ( k5_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['99','105'])).

thf('107',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('108',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('112',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('115',plain,(
    ! [X30: $i] :
      ( ( ( k5_relat_1 @ X30 @ ( k6_relat_1 @ ( k2_relat_1 @ X30 ) ) )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('116',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('119',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('120',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('121',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('124',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('125',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X26 ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('126',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('130',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['124','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['123','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','136'])).

thf('138',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('141',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','139','140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['109','144'])).

thf('146',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','79'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','52','80','81','87','88','89','90','91','92','93','94','95','96','97','98','145','150','153','154','155','156','157','158'])).

thf('160',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['4','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('162',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X19 @ X20 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('163',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( X0
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('167',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['162','168'])).

thf('170',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('171',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('172',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('173',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['161','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','52','80','81','87','88','89','90','91','92','93','94','95','96','97','98','145','150','153','154','155','156','157','158'])).

thf('180',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','52','80','81','87','88','89','90','91','92','93','94','95','96','97','98','145','150','153','154','155','156','157','158'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['178','179','180','181'])).

thf('183',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['160','182'])).

thf('184',plain,(
    $false ),
    inference(simplify,[status(thm)],['183'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1hwXjNBib1
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 21:00:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 6.80/7.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.80/7.01  % Solved by: fo/fo7.sh
% 6.80/7.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.80/7.01  % done 5648 iterations in 6.540s
% 6.80/7.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.80/7.01  % SZS output start Refutation
% 6.80/7.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.80/7.01  thf(sk_A_type, type, sk_A: $i).
% 6.80/7.01  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 6.80/7.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.80/7.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.80/7.01  thf(sk_B_type, type, sk_B: $i).
% 6.80/7.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.80/7.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.80/7.01  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.80/7.01  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.80/7.01  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.80/7.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.80/7.01  thf(t94_relat_1, axiom,
% 6.80/7.01    (![A:$i,B:$i]:
% 6.80/7.01     ( ( v1_relat_1 @ B ) =>
% 6.80/7.01       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 6.80/7.01  thf('0', plain,
% 6.80/7.01      (![X31 : $i, X32 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 6.80/7.01          | ~ (v1_relat_1 @ X32))),
% 6.80/7.01      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.80/7.01  thf(t43_funct_1, conjecture,
% 6.80/7.01    (![A:$i,B:$i]:
% 6.80/7.01     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 6.80/7.01       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.80/7.01  thf(zf_stmt_0, negated_conjecture,
% 6.80/7.01    (~( ![A:$i,B:$i]:
% 6.80/7.01        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 6.80/7.01          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 6.80/7.01    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 6.80/7.01  thf('1', plain,
% 6.80/7.01      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 6.80/7.01         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 6.80/7.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.80/7.01  thf('2', plain,
% 6.80/7.01      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 6.80/7.01          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 6.80/7.01        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 6.80/7.01      inference('sup-', [status(thm)], ['0', '1'])).
% 6.80/7.01  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 6.80/7.01  thf('3', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('4', plain,
% 6.80/7.01      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 6.80/7.01         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 6.80/7.01      inference('demod', [status(thm)], ['2', '3'])).
% 6.80/7.01  thf(d10_xboole_0, axiom,
% 6.80/7.01    (![A:$i,B:$i]:
% 6.80/7.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.80/7.01  thf('5', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.80/7.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.80/7.01  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.80/7.01      inference('simplify', [status(thm)], ['5'])).
% 6.80/7.01  thf(t77_relat_1, axiom,
% 6.80/7.01    (![A:$i,B:$i]:
% 6.80/7.01     ( ( v1_relat_1 @ B ) =>
% 6.80/7.01       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 6.80/7.01         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 6.80/7.01  thf('7', plain,
% 6.80/7.01      (![X28 : $i, X29 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 6.80/7.01          | ((k5_relat_1 @ (k6_relat_1 @ X29) @ X28) = (X28))
% 6.80/7.01          | ~ (v1_relat_1 @ X28))),
% 6.80/7.01      inference('cnf', [status(esa)], [t77_relat_1])).
% 6.80/7.01  thf('8', plain,
% 6.80/7.01      (![X0 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X0)
% 6.80/7.01          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 6.80/7.01      inference('sup-', [status(thm)], ['6', '7'])).
% 6.80/7.01  thf(t17_xboole_1, axiom,
% 6.80/7.01    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 6.80/7.01  thf('9', plain,
% 6.80/7.01      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 6.80/7.01      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.80/7.01  thf(t71_relat_1, axiom,
% 6.80/7.01    (![A:$i]:
% 6.80/7.01     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 6.80/7.01       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 6.80/7.01  thf('10', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('11', plain,
% 6.80/7.01      (![X28 : $i, X29 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 6.80/7.01          | ((k5_relat_1 @ (k6_relat_1 @ X29) @ X28) = (X28))
% 6.80/7.01          | ~ (v1_relat_1 @ X28))),
% 6.80/7.01      inference('cnf', [status(esa)], [t77_relat_1])).
% 6.80/7.01  thf('12', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (r1_tarski @ X0 @ X1)
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.80/7.01          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 6.80/7.01              = (k6_relat_1 @ X0)))),
% 6.80/7.01      inference('sup-', [status(thm)], ['10', '11'])).
% 6.80/7.01  thf('13', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('14', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (r1_tarski @ X0 @ X1)
% 6.80/7.01          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 6.80/7.01              = (k6_relat_1 @ X0)))),
% 6.80/7.01      inference('demod', [status(thm)], ['12', '13'])).
% 6.80/7.01  thf('15', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 6.80/7.01           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 6.80/7.01           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('sup-', [status(thm)], ['9', '14'])).
% 6.80/7.01  thf(t55_relat_1, axiom,
% 6.80/7.01    (![A:$i]:
% 6.80/7.01     ( ( v1_relat_1 @ A ) =>
% 6.80/7.01       ( ![B:$i]:
% 6.80/7.01         ( ( v1_relat_1 @ B ) =>
% 6.80/7.01           ( ![C:$i]:
% 6.80/7.01             ( ( v1_relat_1 @ C ) =>
% 6.80/7.01               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 6.80/7.01                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 6.80/7.01  thf('16', plain,
% 6.80/7.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X21)
% 6.80/7.01          | ((k5_relat_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 6.80/7.01              = (k5_relat_1 @ X22 @ (k5_relat_1 @ X21 @ X23)))
% 6.80/7.01          | ~ (v1_relat_1 @ X23)
% 6.80/7.01          | ~ (v1_relat_1 @ X22))),
% 6.80/7.01      inference('cnf', [status(esa)], [t55_relat_1])).
% 6.80/7.01  thf(t76_relat_1, axiom,
% 6.80/7.01    (![A:$i,B:$i]:
% 6.80/7.01     ( ( v1_relat_1 @ B ) =>
% 6.80/7.01       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 6.80/7.01         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 6.80/7.01  thf('17', plain,
% 6.80/7.01      (![X26 : $i, X27 : $i]:
% 6.80/7.01         ((r1_tarski @ (k5_relat_1 @ X26 @ (k6_relat_1 @ X27)) @ X26)
% 6.80/7.01          | ~ (v1_relat_1 @ X26))),
% 6.80/7.01      inference('cnf', [status(esa)], [t76_relat_1])).
% 6.80/7.01  thf('18', plain,
% 6.80/7.01      (![X0 : $i, X2 : $i]:
% 6.80/7.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.80/7.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.80/7.01  thf('19', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X0)
% 6.80/7.01          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 6.80/7.01          | ((X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 6.80/7.01      inference('sup-', [status(thm)], ['17', '18'])).
% 6.80/7.01  thf('20', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k5_relat_1 @ X2 @ X1) @ 
% 6.80/7.01             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 6.80/7.01          | ~ (v1_relat_1 @ X2)
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ X1)
% 6.80/7.01          | ((k5_relat_1 @ X2 @ X1)
% 6.80/7.01              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k6_relat_1 @ X0)))
% 6.80/7.01          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 6.80/7.01      inference('sup-', [status(thm)], ['16', '19'])).
% 6.80/7.01  thf('21', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('22', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k5_relat_1 @ X2 @ X1) @ 
% 6.80/7.01             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 6.80/7.01          | ~ (v1_relat_1 @ X2)
% 6.80/7.01          | ~ (v1_relat_1 @ X1)
% 6.80/7.01          | ((k5_relat_1 @ X2 @ X1)
% 6.80/7.01              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k6_relat_1 @ X0)))
% 6.80/7.01          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)], ['20', '21'])).
% 6.80/7.01  thf('23', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 6.80/7.01             (k5_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 6.80/7.01          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)))
% 6.80/7.01          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X1))
% 6.80/7.01              = (k5_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 6.80/7.01                 (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 6.80/7.01          | ~ (v1_relat_1 @ X2))),
% 6.80/7.01      inference('sup-', [status(thm)], ['15', '22'])).
% 6.80/7.01  thf('24', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('25', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 6.80/7.01             (k5_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 6.80/7.01          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)))
% 6.80/7.01          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X1))
% 6.80/7.01              = (k5_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 6.80/7.01                 (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 6.80/7.01          | ~ (v1_relat_1 @ X2))),
% 6.80/7.01      inference('demod', [status(thm)], ['23', '24'])).
% 6.80/7.01  thf('26', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (r1_tarski @ 
% 6.80/7.01             (k5_relat_1 @ 
% 6.80/7.01              (k6_relat_1 @ 
% 6.80/7.01               (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 6.80/7.01              (k6_relat_1 @ X1)) @ 
% 6.80/7.01             (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 6.80/7.01          | ~ (v1_relat_1 @ 
% 6.80/7.01               (k6_relat_1 @ 
% 6.80/7.01                (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))
% 6.80/7.01          | ((k5_relat_1 @ 
% 6.80/7.01              (k6_relat_1 @ 
% 6.80/7.01               (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 6.80/7.01              (k6_relat_1 @ X1))
% 6.80/7.01              = (k5_relat_1 @ 
% 6.80/7.01                 (k5_relat_1 @ 
% 6.80/7.01                  (k6_relat_1 @ 
% 6.80/7.01                   (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 6.80/7.01                  (k6_relat_1 @ X1)) @ 
% 6.80/7.01                 (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 6.80/7.01          | ~ (v1_relat_1 @ 
% 6.80/7.01               (k5_relat_1 @ 
% 6.80/7.01                (k6_relat_1 @ 
% 6.80/7.01                 (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 6.80/7.01                (k6_relat_1 @ X1))))),
% 6.80/7.01      inference('sup-', [status(thm)], ['8', '25'])).
% 6.80/7.01  thf('27', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('28', plain,
% 6.80/7.01      (![X31 : $i, X32 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 6.80/7.01          | ~ (v1_relat_1 @ X32))),
% 6.80/7.01      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.80/7.01  thf('29', plain,
% 6.80/7.01      (![X26 : $i, X27 : $i]:
% 6.80/7.01         ((r1_tarski @ (k5_relat_1 @ X26 @ (k6_relat_1 @ X27)) @ X26)
% 6.80/7.01          | ~ (v1_relat_1 @ X26))),
% 6.80/7.01      inference('cnf', [status(esa)], [t76_relat_1])).
% 6.80/7.01  thf('30', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.80/7.01           (k6_relat_1 @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['28', '29'])).
% 6.80/7.01  thf('31', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('32', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('33', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 6.80/7.01      inference('demod', [status(thm)], ['30', '31', '32'])).
% 6.80/7.01  thf(t28_xboole_1, axiom,
% 6.80/7.01    (![A:$i,B:$i]:
% 6.80/7.01     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.80/7.01  thf('34', plain,
% 6.80/7.01      (![X5 : $i, X6 : $i]:
% 6.80/7.01         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 6.80/7.01      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.80/7.01  thf('35', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k3_xboole_0 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.80/7.01           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.80/7.01      inference('sup-', [status(thm)], ['33', '34'])).
% 6.80/7.01  thf(commutativity_k2_tarski, axiom,
% 6.80/7.01    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 6.80/7.01  thf('36', plain,
% 6.80/7.01      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 6.80/7.01      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 6.80/7.01  thf(t12_setfam_1, axiom,
% 6.80/7.01    (![A:$i,B:$i]:
% 6.80/7.01     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.80/7.01  thf('37', plain,
% 6.80/7.01      (![X11 : $i, X12 : $i]:
% 6.80/7.01         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 6.80/7.01      inference('cnf', [status(esa)], [t12_setfam_1])).
% 6.80/7.01  thf('38', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 6.80/7.01      inference('sup+', [status(thm)], ['36', '37'])).
% 6.80/7.01  thf('39', plain,
% 6.80/7.01      (![X11 : $i, X12 : $i]:
% 6.80/7.01         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 6.80/7.01      inference('cnf', [status(esa)], [t12_setfam_1])).
% 6.80/7.01  thf('40', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.80/7.01      inference('sup+', [status(thm)], ['38', '39'])).
% 6.80/7.01  thf('41', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 6.80/7.01           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.80/7.01      inference('demod', [status(thm)], ['35', '40'])).
% 6.80/7.01  thf('42', plain,
% 6.80/7.01      (![X31 : $i, X32 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 6.80/7.01          | ~ (v1_relat_1 @ X32))),
% 6.80/7.01      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.80/7.01  thf('43', plain,
% 6.80/7.01      (![X26 : $i, X27 : $i]:
% 6.80/7.01         ((r1_tarski @ (k5_relat_1 @ X26 @ (k6_relat_1 @ X27)) @ X26)
% 6.80/7.01          | ~ (v1_relat_1 @ X26))),
% 6.80/7.01      inference('cnf', [status(esa)], [t76_relat_1])).
% 6.80/7.01  thf('44', plain,
% 6.80/7.01      (![X5 : $i, X6 : $i]:
% 6.80/7.01         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 6.80/7.01      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.80/7.01  thf('45', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X0)
% 6.80/7.01          | ((k3_xboole_0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 6.80/7.01              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 6.80/7.01      inference('sup-', [status(thm)], ['43', '44'])).
% 6.80/7.01  thf('46', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (((k3_xboole_0 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.80/7.01            (k6_relat_1 @ X0))
% 6.80/7.01            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['42', '45'])).
% 6.80/7.01  thf('47', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('48', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('49', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k3_xboole_0 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.80/7.01           (k6_relat_1 @ X0))
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)], ['46', '47', '48'])).
% 6.80/7.01  thf('50', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.80/7.01      inference('sup+', [status(thm)], ['38', '39'])).
% 6.80/7.01  thf('51', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 6.80/7.01           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)], ['49', '50'])).
% 6.80/7.01  thf('52', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['41', '51'])).
% 6.80/7.01  thf('53', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.80/7.01      inference('sup+', [status(thm)], ['38', '39'])).
% 6.80/7.01  thf(t100_relat_1, axiom,
% 6.80/7.01    (![A:$i,B:$i,C:$i]:
% 6.80/7.01     ( ( v1_relat_1 @ C ) =>
% 6.80/7.01       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 6.80/7.01         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 6.80/7.01  thf('54', plain,
% 6.80/7.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 6.80/7.01            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 6.80/7.01          | ~ (v1_relat_1 @ X16))),
% 6.80/7.01      inference('cnf', [status(esa)], [t100_relat_1])).
% 6.80/7.01  thf(t192_relat_1, axiom,
% 6.80/7.01    (![A:$i,B:$i]:
% 6.80/7.01     ( ( v1_relat_1 @ B ) =>
% 6.80/7.01       ( ( k7_relat_1 @ B @ A ) =
% 6.80/7.01         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 6.80/7.01  thf('55', plain,
% 6.80/7.01      (![X19 : $i, X20 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X19 @ X20)
% 6.80/7.01            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ (k1_relat_1 @ X19) @ X20)))
% 6.80/7.01          | ~ (v1_relat_1 @ X19))),
% 6.80/7.01      inference('cnf', [status(esa)], [t192_relat_1])).
% 6.80/7.01  thf('56', plain,
% 6.80/7.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 6.80/7.01            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 6.80/7.01          | ~ (v1_relat_1 @ X16))),
% 6.80/7.01      inference('cnf', [status(esa)], [t100_relat_1])).
% 6.80/7.01  thf('57', plain,
% 6.80/7.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 6.80/7.01            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 6.80/7.01          | ~ (v1_relat_1 @ X16))),
% 6.80/7.01      inference('cnf', [status(esa)], [t100_relat_1])).
% 6.80/7.01  thf('58', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.80/7.01      inference('sup+', [status(thm)], ['38', '39'])).
% 6.80/7.01  thf('59', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('60', plain,
% 6.80/7.01      (![X19 : $i, X20 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X19 @ X20)
% 6.80/7.01            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ (k1_relat_1 @ X19) @ X20)))
% 6.80/7.01          | ~ (v1_relat_1 @ X19))),
% 6.80/7.01      inference('cnf', [status(esa)], [t192_relat_1])).
% 6.80/7.01  thf('61', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['59', '60'])).
% 6.80/7.01  thf('62', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('63', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)], ['61', '62'])).
% 6.80/7.01  thf('64', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['58', '63'])).
% 6.80/7.01  thf('65', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['57', '64'])).
% 6.80/7.01  thf('66', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('67', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 6.80/7.01      inference('demod', [status(thm)], ['65', '66'])).
% 6.80/7.01  thf('68', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 6.80/7.01            = (k7_relat_1 @ 
% 6.80/7.01               (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['56', '67'])).
% 6.80/7.01  thf('69', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('70', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 6.80/7.01           = (k7_relat_1 @ 
% 6.80/7.01              (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2))),
% 6.80/7.01      inference('demod', [status(thm)], ['68', '69'])).
% 6.80/7.01  thf('71', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k6_relat_1 @ X1) @ 
% 6.80/7.01            (k3_xboole_0 @ 
% 6.80/7.01             (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ X2))
% 6.80/7.01            = (k7_relat_1 @ 
% 6.80/7.01               (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ X1))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['55', '70'])).
% 6.80/7.01  thf('72', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('73', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 6.80/7.01           = (k7_relat_1 @ 
% 6.80/7.01              (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2))),
% 6.80/7.01      inference('demod', [status(thm)], ['68', '69'])).
% 6.80/7.01  thf('74', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('75', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ 
% 6.80/7.01           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 6.80/7.01      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 6.80/7.01  thf('76', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (((k7_relat_1 @ 
% 6.80/7.01            (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X2 @ X1)) @ X0)
% 6.80/7.01            = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['54', '75'])).
% 6.80/7.01  thf('77', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)], ['61', '62'])).
% 6.80/7.01  thf('78', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('79', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0)
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 6.80/7.01      inference('demod', [status(thm)], ['76', '77', '78'])).
% 6.80/7.01  thf('80', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['53', '79'])).
% 6.80/7.01  thf('81', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 6.80/7.01      inference('demod', [status(thm)], ['65', '66'])).
% 6.80/7.01  thf('82', plain,
% 6.80/7.01      (![X19 : $i, X20 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X19 @ X20)
% 6.80/7.01            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ (k1_relat_1 @ X19) @ X20)))
% 6.80/7.01          | ~ (v1_relat_1 @ X19))),
% 6.80/7.01      inference('cnf', [status(esa)], [t192_relat_1])).
% 6.80/7.01  thf('83', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 6.80/7.01      inference('demod', [status(thm)], ['30', '31', '32'])).
% 6.80/7.01  thf('84', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.80/7.01           (k6_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['82', '83'])).
% 6.80/7.01  thf('85', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('86', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('87', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.80/7.01          (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.80/7.01      inference('demod', [status(thm)], ['84', '85', '86'])).
% 6.80/7.01  thf('88', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('89', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('90', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('91', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('92', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['41', '51'])).
% 6.80/7.01  thf('93', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['53', '79'])).
% 6.80/7.01  thf('94', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 6.80/7.01      inference('demod', [status(thm)], ['65', '66'])).
% 6.80/7.01  thf('95', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('96', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['41', '51'])).
% 6.80/7.01  thf('97', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['53', '79'])).
% 6.80/7.01  thf('98', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 6.80/7.01      inference('demod', [status(thm)], ['65', '66'])).
% 6.80/7.01  thf('99', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['41', '51'])).
% 6.80/7.01  thf('100', plain,
% 6.80/7.01      (![X31 : $i, X32 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 6.80/7.01          | ~ (v1_relat_1 @ X32))),
% 6.80/7.01      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.80/7.01  thf('101', plain,
% 6.80/7.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X21)
% 6.80/7.01          | ((k5_relat_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 6.80/7.01              = (k5_relat_1 @ X22 @ (k5_relat_1 @ X21 @ X23)))
% 6.80/7.01          | ~ (v1_relat_1 @ X23)
% 6.80/7.01          | ~ (v1_relat_1 @ X22))),
% 6.80/7.01      inference('cnf', [status(esa)], [t55_relat_1])).
% 6.80/7.01  thf('102', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 6.80/7.01            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 6.80/7.01          | ~ (v1_relat_1 @ X1)
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ X2)
% 6.80/7.01          | ~ (v1_relat_1 @ X1))),
% 6.80/7.01      inference('sup+', [status(thm)], ['100', '101'])).
% 6.80/7.01  thf('103', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('104', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 6.80/7.01            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 6.80/7.01          | ~ (v1_relat_1 @ X1)
% 6.80/7.01          | ~ (v1_relat_1 @ X2)
% 6.80/7.01          | ~ (v1_relat_1 @ X1))),
% 6.80/7.01      inference('demod', [status(thm)], ['102', '103'])).
% 6.80/7.01  thf('105', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X2)
% 6.80/7.01          | ~ (v1_relat_1 @ X1)
% 6.80/7.01          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 6.80/7.01              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 6.80/7.01      inference('simplify', [status(thm)], ['104'])).
% 6.80/7.01  thf('106', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 6.80/7.01            (k6_relat_1 @ X1))
% 6.80/7.01            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 6.80/7.01               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['99', '105'])).
% 6.80/7.01  thf('107', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('108', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('109', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 6.80/7.01           (k6_relat_1 @ X1))
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 6.80/7.01              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.80/7.01      inference('demod', [status(thm)], ['106', '107', '108'])).
% 6.80/7.01  thf('110', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['41', '51'])).
% 6.80/7.01  thf('111', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X2)
% 6.80/7.01          | ~ (v1_relat_1 @ X1)
% 6.80/7.01          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 6.80/7.01              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 6.80/7.01      inference('simplify', [status(thm)], ['104'])).
% 6.80/7.01  thf('112', plain,
% 6.80/7.01      (![X31 : $i, X32 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 6.80/7.01          | ~ (v1_relat_1 @ X32))),
% 6.80/7.01      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.80/7.01  thf('113', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 6.80/7.01            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ X2)
% 6.80/7.01          | ~ (v1_relat_1 @ X0)
% 6.80/7.01          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['111', '112'])).
% 6.80/7.01  thf('114', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.80/7.01          | ((k7_relat_1 @ 
% 6.80/7.01              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)) @ X2)
% 6.80/7.01              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 6.80/7.01                 (k6_relat_1 @ X1))))),
% 6.80/7.01      inference('sup-', [status(thm)], ['110', '113'])).
% 6.80/7.01  thf(t80_relat_1, axiom,
% 6.80/7.01    (![A:$i]:
% 6.80/7.01     ( ( v1_relat_1 @ A ) =>
% 6.80/7.01       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 6.80/7.01  thf('115', plain,
% 6.80/7.01      (![X30 : $i]:
% 6.80/7.01         (((k5_relat_1 @ X30 @ (k6_relat_1 @ (k2_relat_1 @ X30))) = (X30))
% 6.80/7.01          | ~ (v1_relat_1 @ X30))),
% 6.80/7.01      inference('cnf', [status(esa)], [t80_relat_1])).
% 6.80/7.01  thf('116', plain,
% 6.80/7.01      (![X31 : $i, X32 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 6.80/7.01          | ~ (v1_relat_1 @ X32))),
% 6.80/7.01      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.80/7.01  thf('117', plain,
% 6.80/7.01      (![X0 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 6.80/7.01            = (k6_relat_1 @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 6.80/7.01      inference('sup+', [status(thm)], ['115', '116'])).
% 6.80/7.01  thf('118', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('119', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('120', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('121', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('122', plain,
% 6.80/7.01      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 6.80/7.01      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 6.80/7.01  thf('123', plain,
% 6.80/7.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 6.80/7.01            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 6.80/7.01          | ~ (v1_relat_1 @ X16))),
% 6.80/7.01      inference('cnf', [status(esa)], [t100_relat_1])).
% 6.80/7.01  thf('124', plain,
% 6.80/7.01      (![X31 : $i, X32 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 6.80/7.01          | ~ (v1_relat_1 @ X32))),
% 6.80/7.01      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.80/7.01  thf('125', plain,
% 6.80/7.01      (![X26 : $i, X27 : $i]:
% 6.80/7.01         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X27) @ X26) @ X26)
% 6.80/7.01          | ~ (v1_relat_1 @ X26))),
% 6.80/7.01      inference('cnf', [status(esa)], [t76_relat_1])).
% 6.80/7.01  thf('126', plain,
% 6.80/7.01      (![X5 : $i, X6 : $i]:
% 6.80/7.01         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 6.80/7.01      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.80/7.01  thf('127', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X0)
% 6.80/7.01          | ((k3_xboole_0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 6.80/7.01              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.80/7.01      inference('sup-', [status(thm)], ['125', '126'])).
% 6.80/7.01  thf('128', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.80/7.01      inference('sup+', [status(thm)], ['38', '39'])).
% 6.80/7.01  thf('129', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X0)
% 6.80/7.01          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.80/7.01              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.80/7.01      inference('demod', [status(thm)], ['127', '128'])).
% 6.80/7.01  thf(fc1_relat_1, axiom,
% 6.80/7.01    (![A:$i,B:$i]:
% 6.80/7.01     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.80/7.01  thf('130', plain,
% 6.80/7.01      (![X14 : $i, X15 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k3_xboole_0 @ X14 @ X15)))),
% 6.80/7.01      inference('cnf', [status(esa)], [fc1_relat_1])).
% 6.80/7.01  thf('131', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ X0)
% 6.80/7.01          | ~ (v1_relat_1 @ X0))),
% 6.80/7.01      inference('sup+', [status(thm)], ['129', '130'])).
% 6.80/7.01  thf('132', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X0)
% 6.80/7.01          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.80/7.01      inference('simplify', [status(thm)], ['131'])).
% 6.80/7.01  thf('133', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ X1)
% 6.80/7.01          | ~ (v1_relat_1 @ X1))),
% 6.80/7.01      inference('sup+', [status(thm)], ['124', '132'])).
% 6.80/7.01  thf('134', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 6.80/7.01      inference('simplify', [status(thm)], ['133'])).
% 6.80/7.01  thf('135', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ X2)
% 6.80/7.01          | ~ (v1_relat_1 @ X2))),
% 6.80/7.01      inference('sup+', [status(thm)], ['123', '134'])).
% 6.80/7.01  thf('136', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X2)
% 6.80/7.01          | (v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 6.80/7.01      inference('simplify', [status(thm)], ['135'])).
% 6.80/7.01  thf('137', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['122', '136'])).
% 6.80/7.01  thf('138', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('139', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 6.80/7.01      inference('demod', [status(thm)], ['137', '138'])).
% 6.80/7.01  thf('140', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('141', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('142', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['41', '51'])).
% 6.80/7.01  thf('143', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 6.80/7.01           (k6_relat_1 @ X1))
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 6.80/7.01              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.80/7.01      inference('demod', [status(thm)], ['106', '107', '108'])).
% 6.80/7.01  thf('144', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 6.80/7.01              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.80/7.01      inference('demod', [status(thm)],
% 6.80/7.01                ['114', '139', '140', '141', '142', '143'])).
% 6.80/7.01  thf('145', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 6.80/7.01           (k6_relat_1 @ X1))
% 6.80/7.01           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 6.80/7.01      inference('demod', [status(thm)], ['109', '144'])).
% 6.80/7.01  thf('146', plain,
% 6.80/7.01      (![X31 : $i, X32 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 6.80/7.01          | ~ (v1_relat_1 @ X32))),
% 6.80/7.01      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.80/7.01  thf('147', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 6.80/7.01           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 6.80/7.01           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('sup-', [status(thm)], ['9', '14'])).
% 6.80/7.01  thf('148', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 6.80/7.01            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 6.80/7.01      inference('sup+', [status(thm)], ['146', '147'])).
% 6.80/7.01  thf('149', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('150', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 6.80/7.01           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)], ['148', '149'])).
% 6.80/7.01  thf('151', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.80/7.01      inference('sup+', [status(thm)], ['38', '39'])).
% 6.80/7.01  thf('152', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 6.80/7.01           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)], ['148', '149'])).
% 6.80/7.01  thf('153', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 6.80/7.01           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['151', '152'])).
% 6.80/7.01  thf('154', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('155', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['41', '51'])).
% 6.80/7.01  thf('156', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['53', '79'])).
% 6.80/7.01  thf('157', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 6.80/7.01      inference('demod', [status(thm)], ['65', '66'])).
% 6.80/7.01  thf('158', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 6.80/7.01      inference('demod', [status(thm)], ['137', '138'])).
% 6.80/7.01  thf('159', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)],
% 6.80/7.01                ['26', '27', '52', '80', '81', '87', '88', '89', '90', '91', 
% 6.80/7.01                 '92', '93', '94', '95', '96', '97', '98', '145', '150', 
% 6.80/7.01                 '153', '154', '155', '156', '157', '158'])).
% 6.80/7.01  thf('160', plain,
% 6.80/7.01      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 6.80/7.01         != (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 6.80/7.01      inference('demod', [status(thm)], ['4', '159'])).
% 6.80/7.01  thf('161', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.80/7.01      inference('sup+', [status(thm)], ['38', '39'])).
% 6.80/7.01  thf('162', plain,
% 6.80/7.01      (![X19 : $i, X20 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X19 @ X20)
% 6.80/7.01            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ (k1_relat_1 @ X19) @ X20)))
% 6.80/7.01          | ~ (v1_relat_1 @ X19))),
% 6.80/7.01      inference('cnf', [status(esa)], [t192_relat_1])).
% 6.80/7.01  thf('163', plain,
% 6.80/7.01      (![X31 : $i, X32 : $i]:
% 6.80/7.01         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 6.80/7.01          | ~ (v1_relat_1 @ X32))),
% 6.80/7.01      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.80/7.01  thf('164', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (v1_relat_1 @ X0)
% 6.80/7.01          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 6.80/7.01          | ((X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 6.80/7.01      inference('sup-', [status(thm)], ['17', '18'])).
% 6.80/7.01  thf('165', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k6_relat_1 @ X0) @ 
% 6.80/7.01             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 6.80/7.01          | ((k6_relat_1 @ X0)
% 6.80/7.01              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.80/7.01      inference('sup-', [status(thm)], ['163', '164'])).
% 6.80/7.01  thf('166', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('167', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('168', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k6_relat_1 @ X0) @ 
% 6.80/7.01             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.80/7.01          | ((k6_relat_1 @ X0)
% 6.80/7.01              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 6.80/7.01      inference('demod', [status(thm)], ['165', '166', '167'])).
% 6.80/7.01  thf('169', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (r1_tarski @ 
% 6.80/7.01             (k6_relat_1 @ 
% 6.80/7.01              (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 6.80/7.01             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.80/7.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 6.80/7.01          | ((k6_relat_1 @ 
% 6.80/7.01              (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 6.80/7.01              = (k5_relat_1 @ 
% 6.80/7.01                 (k6_relat_1 @ 
% 6.80/7.01                  (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 6.80/7.01                 (k6_relat_1 @ X1))))),
% 6.80/7.01      inference('sup-', [status(thm)], ['162', '168'])).
% 6.80/7.01  thf('170', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('171', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.80/7.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.80/7.01  thf('172', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('173', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.80/7.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.80/7.01  thf('174', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.80/7.01             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.80/7.01          | ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 6.80/7.01              = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.80/7.01                 (k6_relat_1 @ X1))))),
% 6.80/7.01      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 6.80/7.01  thf('175', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 6.80/7.01      inference('sup+', [status(thm)], ['41', '51'])).
% 6.80/7.01  thf('176', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)], ['61', '62'])).
% 6.80/7.01  thf('177', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.80/7.01             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.80/7.01          | ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 6.80/7.01              = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.80/7.01      inference('demod', [status(thm)], ['174', '175', '176'])).
% 6.80/7.01  thf('178', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.80/7.01             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 6.80/7.01          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 6.80/7.01              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 6.80/7.01      inference('sup-', [status(thm)], ['161', '177'])).
% 6.80/7.01  thf('179', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)],
% 6.80/7.01                ['26', '27', '52', '80', '81', '87', '88', '89', '90', '91', 
% 6.80/7.01                 '92', '93', '94', '95', '96', '97', '98', '145', '150', 
% 6.80/7.01                 '153', '154', '155', '156', '157', '158'])).
% 6.80/7.01  thf('180', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.80/7.01      inference('simplify', [status(thm)], ['5'])).
% 6.80/7.01  thf('181', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.80/7.01      inference('demod', [status(thm)],
% 6.80/7.01                ['26', '27', '52', '80', '81', '87', '88', '89', '90', '91', 
% 6.80/7.01                 '92', '93', '94', '95', '96', '97', '98', '145', '150', 
% 6.80/7.01                 '153', '154', '155', '156', '157', '158'])).
% 6.80/7.01  thf('182', plain,
% 6.80/7.01      (![X0 : $i, X1 : $i]:
% 6.80/7.01         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.80/7.01           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 6.80/7.01      inference('demod', [status(thm)], ['178', '179', '180', '181'])).
% 6.80/7.01  thf('183', plain,
% 6.80/7.01      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 6.80/7.01         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 6.80/7.01      inference('demod', [status(thm)], ['160', '182'])).
% 6.80/7.01  thf('184', plain, ($false), inference('simplify', [status(thm)], ['183'])).
% 6.80/7.01  
% 6.80/7.01  % SZS output end Refutation
% 6.80/7.01  
% 6.80/7.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
