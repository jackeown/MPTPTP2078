%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b0tuW3vYpN

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:23 EST 2020

% Result     : Theorem 17.15s
% Output     : Refutation 17.15s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 185 expanded)
%              Number of leaves         :   40 (  72 expanded)
%              Depth                    :   25
%              Number of atoms          : 1125 (1483 expanded)
%              Number of equality atoms :   79 ( 102 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
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

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X29 ) @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X27 @ X26 ) )
        = ( k10_relat_1 @ X27 @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
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

thf('11',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X28: $i] :
      ( ( ( k2_relat_1 @ X28 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X19: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('20',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('21',plain,(
    ! [X33: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X33 ) )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('22',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('23',plain,(
    ! [X19: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('24',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X29 ) @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('35',plain,(
    ! [X33: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X33 ) )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X29 ) @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X33: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X33 ) )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['32','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','51'])).

thf('53',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','54'])).

thf('56',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','58'])).

thf('60',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k9_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('71',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('74',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('77',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75','78'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('80',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('81',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('82',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k5_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('85',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('86',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['83','90'])).

thf(t163_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) @ ( k9_relat_1 @ ( k4_relat_1 @ B ) @ ( k9_relat_1 @ B @ A ) ) ) ) )).

thf('92',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X24 ) @ X25 ) @ ( k9_relat_1 @ ( k4_relat_1 @ X24 ) @ ( k9_relat_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t163_relat_1])).

thf('93',plain,
    ( ( r1_tarski @ sk_A @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['0','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b0tuW3vYpN
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.15/17.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.15/17.35  % Solved by: fo/fo7.sh
% 17.15/17.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.15/17.35  % done 3572 iterations in 16.891s
% 17.15/17.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.15/17.35  % SZS output start Refutation
% 17.15/17.35  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 17.15/17.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.15/17.35  thf(sk_B_type, type, sk_B: $i).
% 17.15/17.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.15/17.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.15/17.35  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 17.15/17.35  thf(sk_A_type, type, sk_A: $i).
% 17.15/17.35  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 17.15/17.35  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 17.15/17.35  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 17.15/17.35  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.15/17.35  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 17.15/17.35  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 17.15/17.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.15/17.35  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 17.15/17.35  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 17.15/17.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.15/17.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.15/17.35  thf(t146_funct_1, conjecture,
% 17.15/17.35    (![A:$i,B:$i]:
% 17.15/17.35     ( ( v1_relat_1 @ B ) =>
% 17.15/17.35       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 17.15/17.35         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 17.15/17.35  thf(zf_stmt_0, negated_conjecture,
% 17.15/17.35    (~( ![A:$i,B:$i]:
% 17.15/17.35        ( ( v1_relat_1 @ B ) =>
% 17.15/17.35          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 17.15/17.35            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 17.15/17.35    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 17.15/17.35  thf('0', plain,
% 17.15/17.35      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 17.15/17.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.15/17.35  thf(involutiveness_k4_relat_1, axiom,
% 17.15/17.35    (![A:$i]:
% 17.15/17.35     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 17.15/17.35  thf('1', plain,
% 17.15/17.35      (![X19 : $i]:
% 17.15/17.35         (((k4_relat_1 @ (k4_relat_1 @ X19)) = (X19)) | ~ (v1_relat_1 @ X19))),
% 17.15/17.35      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 17.15/17.35  thf(t94_relat_1, axiom,
% 17.15/17.35    (![A:$i,B:$i]:
% 17.15/17.35     ( ( v1_relat_1 @ B ) =>
% 17.15/17.35       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 17.15/17.35  thf('2', plain,
% 17.15/17.35      (![X34 : $i, X35 : $i]:
% 17.15/17.35         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 17.15/17.35          | ~ (v1_relat_1 @ X35))),
% 17.15/17.35      inference('cnf', [status(esa)], [t94_relat_1])).
% 17.15/17.35  thf(t72_relat_1, axiom,
% 17.15/17.35    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 17.15/17.35  thf('3', plain,
% 17.15/17.35      (![X33 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X33)) = (k6_relat_1 @ X33))),
% 17.15/17.35      inference('cnf', [status(esa)], [t72_relat_1])).
% 17.15/17.35  thf(t54_relat_1, axiom,
% 17.15/17.35    (![A:$i]:
% 17.15/17.35     ( ( v1_relat_1 @ A ) =>
% 17.15/17.35       ( ![B:$i]:
% 17.15/17.35         ( ( v1_relat_1 @ B ) =>
% 17.15/17.35           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 17.15/17.35             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 17.15/17.35  thf('4', plain,
% 17.15/17.35      (![X29 : $i, X30 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X29)
% 17.15/17.35          | ((k4_relat_1 @ (k5_relat_1 @ X30 @ X29))
% 17.15/17.35              = (k5_relat_1 @ (k4_relat_1 @ X29) @ (k4_relat_1 @ X30)))
% 17.15/17.35          | ~ (v1_relat_1 @ X30))),
% 17.15/17.35      inference('cnf', [status(esa)], [t54_relat_1])).
% 17.15/17.35  thf('5', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 17.15/17.35            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 17.15/17.35          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 17.15/17.35          | ~ (v1_relat_1 @ X1))),
% 17.15/17.35      inference('sup+', [status(thm)], ['3', '4'])).
% 17.15/17.35  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 17.15/17.35  thf('6', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 17.15/17.35  thf('7', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 17.15/17.35            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 17.15/17.35          | ~ (v1_relat_1 @ X1))),
% 17.15/17.35      inference('demod', [status(thm)], ['5', '6'])).
% 17.15/17.35  thf(t182_relat_1, axiom,
% 17.15/17.35    (![A:$i]:
% 17.15/17.35     ( ( v1_relat_1 @ A ) =>
% 17.15/17.35       ( ![B:$i]:
% 17.15/17.35         ( ( v1_relat_1 @ B ) =>
% 17.15/17.35           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 17.15/17.35             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 17.15/17.35  thf('8', plain,
% 17.15/17.35      (![X26 : $i, X27 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X26)
% 17.15/17.35          | ((k1_relat_1 @ (k5_relat_1 @ X27 @ X26))
% 17.15/17.35              = (k10_relat_1 @ X27 @ (k1_relat_1 @ X26)))
% 17.15/17.35          | ~ (v1_relat_1 @ X27))),
% 17.15/17.35      inference('cnf', [status(esa)], [t182_relat_1])).
% 17.15/17.35  thf('9', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 17.15/17.35            = (k10_relat_1 @ (k4_relat_1 @ X0) @ 
% 17.15/17.35               (k1_relat_1 @ (k6_relat_1 @ X1))))
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 17.15/17.35          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 17.15/17.35      inference('sup+', [status(thm)], ['7', '8'])).
% 17.15/17.35  thf(t71_relat_1, axiom,
% 17.15/17.35    (![A:$i]:
% 17.15/17.35     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 17.15/17.35       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 17.15/17.35  thf('10', plain, (![X31 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X31)) = (X31))),
% 17.15/17.35      inference('cnf', [status(esa)], [t71_relat_1])).
% 17.15/17.35  thf('11', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 17.15/17.35  thf('12', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 17.15/17.35            = (k10_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 17.15/17.35      inference('demod', [status(thm)], ['9', '10', '11'])).
% 17.15/17.35  thf(dt_k4_relat_1, axiom,
% 17.15/17.35    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 17.15/17.35  thf('13', plain,
% 17.15/17.35      (![X15 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X15)) | ~ (v1_relat_1 @ X15))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 17.15/17.35  thf('14', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X0)
% 17.15/17.35          | ((k1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 17.15/17.35              = (k10_relat_1 @ (k4_relat_1 @ X0) @ X1)))),
% 17.15/17.35      inference('clc', [status(thm)], ['12', '13'])).
% 17.15/17.35  thf('15', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k1_relat_1 @ (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 17.15/17.35            = (k10_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ X1))),
% 17.15/17.35      inference('sup+', [status(thm)], ['2', '14'])).
% 17.15/17.35  thf('16', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X1)
% 17.15/17.35          | ((k1_relat_1 @ (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 17.15/17.35              = (k10_relat_1 @ (k4_relat_1 @ X1) @ X0)))),
% 17.15/17.35      inference('simplify', [status(thm)], ['15'])).
% 17.15/17.35  thf(t37_relat_1, axiom,
% 17.15/17.35    (![A:$i]:
% 17.15/17.35     ( ( v1_relat_1 @ A ) =>
% 17.15/17.35       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 17.15/17.35         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 17.15/17.35  thf('17', plain,
% 17.15/17.35      (![X28 : $i]:
% 17.15/17.35         (((k2_relat_1 @ X28) = (k1_relat_1 @ (k4_relat_1 @ X28)))
% 17.15/17.35          | ~ (v1_relat_1 @ X28))),
% 17.15/17.35      inference('cnf', [status(esa)], [t37_relat_1])).
% 17.15/17.35  thf('18', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 17.15/17.35            = (k10_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 17.15/17.35      inference('sup+', [status(thm)], ['16', '17'])).
% 17.15/17.35  thf('19', plain,
% 17.15/17.35      (![X19 : $i]:
% 17.15/17.35         (((k4_relat_1 @ (k4_relat_1 @ X19)) = (X19)) | ~ (v1_relat_1 @ X19))),
% 17.15/17.35      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 17.15/17.35  thf('20', plain,
% 17.15/17.35      (![X34 : $i, X35 : $i]:
% 17.15/17.35         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 17.15/17.35          | ~ (v1_relat_1 @ X35))),
% 17.15/17.35      inference('cnf', [status(esa)], [t94_relat_1])).
% 17.15/17.35  thf('21', plain,
% 17.15/17.35      (![X33 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X33)) = (k6_relat_1 @ X33))),
% 17.15/17.35      inference('cnf', [status(esa)], [t72_relat_1])).
% 17.15/17.35  thf('22', plain,
% 17.15/17.35      (![X15 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X15)) | ~ (v1_relat_1 @ X15))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 17.15/17.35  thf('23', plain,
% 17.15/17.35      (![X19 : $i]:
% 17.15/17.35         (((k4_relat_1 @ (k4_relat_1 @ X19)) = (X19)) | ~ (v1_relat_1 @ X19))),
% 17.15/17.35      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 17.15/17.35  thf('24', plain,
% 17.15/17.35      (![X29 : $i, X30 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X29)
% 17.15/17.35          | ((k4_relat_1 @ (k5_relat_1 @ X30 @ X29))
% 17.15/17.35              = (k5_relat_1 @ (k4_relat_1 @ X29) @ (k4_relat_1 @ X30)))
% 17.15/17.35          | ~ (v1_relat_1 @ X30))),
% 17.15/17.35      inference('cnf', [status(esa)], [t54_relat_1])).
% 17.15/17.35  thf('25', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 17.15/17.35            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 17.15/17.35      inference('sup+', [status(thm)], ['23', '24'])).
% 17.15/17.35  thf('26', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X0)
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | ((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 17.15/17.35              = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))),
% 17.15/17.35      inference('sup-', [status(thm)], ['22', '25'])).
% 17.15/17.35  thf('27', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 17.15/17.35            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ X0))),
% 17.15/17.35      inference('simplify', [status(thm)], ['26'])).
% 17.15/17.35  thf('28', plain,
% 17.15/17.35      (![X15 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X15)) | ~ (v1_relat_1 @ X15))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 17.15/17.35  thf('29', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))),
% 17.15/17.35      inference('sup+', [status(thm)], ['27', '28'])).
% 17.15/17.35  thf('30', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 17.15/17.35          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1))))),
% 17.15/17.35      inference('sup-', [status(thm)], ['21', '29'])).
% 17.15/17.35  thf('31', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 17.15/17.35  thf('32', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1))))),
% 17.15/17.35      inference('demod', [status(thm)], ['30', '31'])).
% 17.15/17.35  thf('33', plain,
% 17.15/17.35      (![X15 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X15)) | ~ (v1_relat_1 @ X15))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 17.15/17.35  thf(t123_relat_1, axiom,
% 17.15/17.35    (![A:$i,B:$i]:
% 17.15/17.35     ( ( v1_relat_1 @ B ) =>
% 17.15/17.35       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 17.15/17.35  thf('34', plain,
% 17.15/17.35      (![X20 : $i, X21 : $i]:
% 17.15/17.35         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 17.15/17.35          | ~ (v1_relat_1 @ X20))),
% 17.15/17.35      inference('cnf', [status(esa)], [t123_relat_1])).
% 17.15/17.35  thf('35', plain,
% 17.15/17.35      (![X33 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X33)) = (k6_relat_1 @ X33))),
% 17.15/17.35      inference('cnf', [status(esa)], [t72_relat_1])).
% 17.15/17.35  thf('36', plain,
% 17.15/17.35      (![X29 : $i, X30 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X29)
% 17.15/17.35          | ((k4_relat_1 @ (k5_relat_1 @ X30 @ X29))
% 17.15/17.35              = (k5_relat_1 @ (k4_relat_1 @ X29) @ (k4_relat_1 @ X30)))
% 17.15/17.35          | ~ (v1_relat_1 @ X30))),
% 17.15/17.35      inference('cnf', [status(esa)], [t54_relat_1])).
% 17.15/17.35  thf('37', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 17.15/17.35            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 17.15/17.35      inference('sup+', [status(thm)], ['35', '36'])).
% 17.15/17.35  thf('38', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 17.15/17.35  thf('39', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 17.15/17.35            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 17.15/17.35          | ~ (v1_relat_1 @ X1))),
% 17.15/17.35      inference('demod', [status(thm)], ['37', '38'])).
% 17.15/17.35  thf('40', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))),
% 17.15/17.35      inference('sup+', [status(thm)], ['27', '28'])).
% 17.15/17.35  thf('41', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ (k6_relat_1 @ X0)))))),
% 17.15/17.35      inference('sup-', [status(thm)], ['39', '40'])).
% 17.15/17.35  thf('42', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 17.15/17.35  thf('43', plain,
% 17.15/17.35      (![X33 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X33)) = (k6_relat_1 @ X33))),
% 17.15/17.35      inference('cnf', [status(esa)], [t72_relat_1])).
% 17.15/17.35  thf('44', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 17.15/17.35      inference('demod', [status(thm)], ['41', '42', '43'])).
% 17.15/17.35  thf('45', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ 
% 17.15/17.35               (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 17.15/17.35      inference('simplify', [status(thm)], ['44'])).
% 17.15/17.35  thf('46', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 17.15/17.35      inference('sup-', [status(thm)], ['34', '45'])).
% 17.15/17.35  thf('47', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | ~ (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0))))),
% 17.15/17.35      inference('simplify', [status(thm)], ['46'])).
% 17.15/17.35  thf('48', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 17.15/17.35      inference('sup-', [status(thm)], ['33', '47'])).
% 17.15/17.35  thf(dt_k8_relat_1, axiom,
% 17.15/17.35    (![A:$i,B:$i]:
% 17.15/17.35     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 17.15/17.35  thf('49', plain,
% 17.15/17.35      (![X17 : $i, X18 : $i]:
% 17.15/17.35         ((v1_relat_1 @ (k8_relat_1 @ X17 @ X18)) | ~ (v1_relat_1 @ X18))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 17.15/17.35  thf('50', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 17.15/17.35          | ~ (v1_relat_1 @ X0))),
% 17.15/17.35      inference('clc', [status(thm)], ['48', '49'])).
% 17.15/17.35  thf('51', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 17.15/17.35          | ~ (v1_relat_1 @ X1))),
% 17.15/17.35      inference('clc', [status(thm)], ['32', '50'])).
% 17.15/17.35  thf('52', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((v1_relat_1 @ (k7_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 17.15/17.35          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 17.15/17.35          | ~ (v1_relat_1 @ X1))),
% 17.15/17.35      inference('sup+', [status(thm)], ['20', '51'])).
% 17.15/17.35  thf('53', plain,
% 17.15/17.35      (![X15 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X15)) | ~ (v1_relat_1 @ X15))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 17.15/17.35  thf('54', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X1)
% 17.15/17.35          | (v1_relat_1 @ (k7_relat_1 @ (k4_relat_1 @ X1) @ X0)))),
% 17.15/17.35      inference('clc', [status(thm)], ['52', '53'])).
% 17.15/17.35  thf('55', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 17.15/17.35      inference('sup+', [status(thm)], ['19', '54'])).
% 17.15/17.35  thf('56', plain,
% 17.15/17.35      (![X15 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X15)) | ~ (v1_relat_1 @ X15))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 17.15/17.35  thf('57', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 17.15/17.35      inference('clc', [status(thm)], ['55', '56'])).
% 17.15/17.35  thf('58', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X1)
% 17.15/17.35          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 17.15/17.35              = (k10_relat_1 @ (k4_relat_1 @ X1) @ X0)))),
% 17.15/17.35      inference('clc', [status(thm)], ['18', '57'])).
% 17.15/17.35  thf('59', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k2_relat_1 @ (k7_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 17.15/17.35            = (k10_relat_1 @ X0 @ X1))
% 17.15/17.35          | ~ (v1_relat_1 @ X0)
% 17.15/17.35          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 17.15/17.35      inference('sup+', [status(thm)], ['1', '58'])).
% 17.15/17.35  thf('60', plain,
% 17.15/17.35      (![X15 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X15)) | ~ (v1_relat_1 @ X15))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 17.15/17.35  thf('61', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X0)
% 17.15/17.35          | ((k2_relat_1 @ (k7_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 17.15/17.35              = (k10_relat_1 @ X0 @ X1)))),
% 17.15/17.35      inference('clc', [status(thm)], ['59', '60'])).
% 17.15/17.35  thf(t148_relat_1, axiom,
% 17.15/17.35    (![A:$i,B:$i]:
% 17.15/17.35     ( ( v1_relat_1 @ B ) =>
% 17.15/17.35       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 17.15/17.35  thf('62', plain,
% 17.15/17.35      (![X22 : $i, X23 : $i]:
% 17.15/17.35         (((k2_relat_1 @ (k7_relat_1 @ X22 @ X23)) = (k9_relat_1 @ X22 @ X23))
% 17.15/17.35          | ~ (v1_relat_1 @ X22))),
% 17.15/17.35      inference('cnf', [status(esa)], [t148_relat_1])).
% 17.15/17.35  thf('63', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (((k10_relat_1 @ X1 @ X0) = (k9_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 17.15/17.35          | ~ (v1_relat_1 @ X1)
% 17.15/17.35          | ~ (v1_relat_1 @ (k4_relat_1 @ X1)))),
% 17.15/17.35      inference('sup+', [status(thm)], ['61', '62'])).
% 17.15/17.35  thf('64', plain,
% 17.15/17.35      (![X15 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X15)) | ~ (v1_relat_1 @ X15))),
% 17.15/17.35      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 17.15/17.35  thf('65', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         (~ (v1_relat_1 @ X1)
% 17.15/17.35          | ((k10_relat_1 @ X1 @ X0) = (k9_relat_1 @ (k4_relat_1 @ X1) @ X0)))),
% 17.15/17.35      inference('clc', [status(thm)], ['63', '64'])).
% 17.15/17.35  thf('66', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 17.15/17.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.15/17.35  thf(t28_xboole_1, axiom,
% 17.15/17.35    (![A:$i,B:$i]:
% 17.15/17.35     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 17.15/17.35  thf('67', plain,
% 17.15/17.35      (![X4 : $i, X5 : $i]:
% 17.15/17.35         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 17.15/17.35      inference('cnf', [status(esa)], [t28_xboole_1])).
% 17.15/17.35  thf('68', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 17.15/17.35      inference('sup-', [status(thm)], ['66', '67'])).
% 17.15/17.35  thf(t100_xboole_1, axiom,
% 17.15/17.35    (![A:$i,B:$i]:
% 17.15/17.35     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 17.15/17.35  thf('69', plain,
% 17.15/17.35      (![X2 : $i, X3 : $i]:
% 17.15/17.35         ((k4_xboole_0 @ X2 @ X3)
% 17.15/17.35           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 17.15/17.35      inference('cnf', [status(esa)], [t100_xboole_1])).
% 17.15/17.35  thf('70', plain,
% 17.15/17.35      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 17.15/17.35         = (k5_xboole_0 @ sk_A @ sk_A))),
% 17.15/17.35      inference('sup+', [status(thm)], ['68', '69'])).
% 17.15/17.35  thf(t92_xboole_1, axiom,
% 17.15/17.35    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 17.15/17.35  thf('71', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 17.15/17.35      inference('cnf', [status(esa)], [t92_xboole_1])).
% 17.15/17.35  thf('72', plain,
% 17.15/17.35      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 17.15/17.35      inference('demod', [status(thm)], ['70', '71'])).
% 17.15/17.35  thf(t98_xboole_1, axiom,
% 17.15/17.35    (![A:$i,B:$i]:
% 17.15/17.35     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 17.15/17.35  thf('73', plain,
% 17.15/17.35      (![X13 : $i, X14 : $i]:
% 17.15/17.35         ((k2_xboole_0 @ X13 @ X14)
% 17.15/17.35           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 17.15/17.35      inference('cnf', [status(esa)], [t98_xboole_1])).
% 17.15/17.35  thf('74', plain,
% 17.15/17.35      (((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 17.15/17.35         = (k5_xboole_0 @ (k1_relat_1 @ sk_B) @ k1_xboole_0))),
% 17.15/17.35      inference('sup+', [status(thm)], ['72', '73'])).
% 17.15/17.35  thf(commutativity_k5_xboole_0, axiom,
% 17.15/17.35    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 17.15/17.35  thf('75', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 17.15/17.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 17.15/17.35  thf('76', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 17.15/17.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 17.15/17.35  thf(t5_boole, axiom,
% 17.15/17.35    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 17.15/17.35  thf('77', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 17.15/17.35      inference('cnf', [status(esa)], [t5_boole])).
% 17.15/17.35  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 17.15/17.35      inference('sup+', [status(thm)], ['76', '77'])).
% 17.15/17.35  thf('79', plain,
% 17.15/17.35      (((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))),
% 17.15/17.35      inference('demod', [status(thm)], ['74', '75', '78'])).
% 17.15/17.35  thf(t95_xboole_1, axiom,
% 17.15/17.35    (![A:$i,B:$i]:
% 17.15/17.35     ( ( k3_xboole_0 @ A @ B ) =
% 17.15/17.35       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 17.15/17.35  thf('80', plain,
% 17.15/17.35      (![X11 : $i, X12 : $i]:
% 17.15/17.35         ((k3_xboole_0 @ X11 @ X12)
% 17.15/17.35           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 17.15/17.35              (k2_xboole_0 @ X11 @ X12)))),
% 17.15/17.35      inference('cnf', [status(esa)], [t95_xboole_1])).
% 17.15/17.35  thf(t91_xboole_1, axiom,
% 17.15/17.35    (![A:$i,B:$i,C:$i]:
% 17.15/17.35     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 17.15/17.35       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 17.15/17.35  thf('81', plain,
% 17.15/17.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 17.15/17.35         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 17.15/17.35           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 17.15/17.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 17.15/17.35  thf('82', plain,
% 17.15/17.35      (![X11 : $i, X12 : $i]:
% 17.15/17.35         ((k3_xboole_0 @ X11 @ X12)
% 17.15/17.35           = (k5_xboole_0 @ X11 @ 
% 17.15/17.35              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 17.15/17.35      inference('demod', [status(thm)], ['80', '81'])).
% 17.15/17.35  thf('83', plain,
% 17.15/17.35      (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 17.15/17.35         = (k5_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 17.15/17.35            (k5_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 17.15/17.35      inference('sup+', [status(thm)], ['79', '82'])).
% 17.15/17.35  thf('84', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 17.15/17.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 17.15/17.35  thf('85', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 17.15/17.35      inference('cnf', [status(esa)], [t92_xboole_1])).
% 17.15/17.35  thf('86', plain,
% 17.15/17.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 17.15/17.35         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 17.15/17.35           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 17.15/17.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 17.15/17.35  thf('87', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 17.15/17.35           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.15/17.35      inference('sup+', [status(thm)], ['85', '86'])).
% 17.15/17.35  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 17.15/17.35      inference('sup+', [status(thm)], ['76', '77'])).
% 17.15/17.35  thf('89', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.15/17.35      inference('demod', [status(thm)], ['87', '88'])).
% 17.15/17.35  thf('90', plain,
% 17.15/17.35      (![X0 : $i, X1 : $i]:
% 17.15/17.35         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.15/17.35      inference('sup+', [status(thm)], ['84', '89'])).
% 17.15/17.35  thf('91', plain, (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 17.15/17.35      inference('demod', [status(thm)], ['83', '90'])).
% 17.15/17.35  thf(t163_relat_1, axiom,
% 17.15/17.35    (![A:$i,B:$i]:
% 17.15/17.35     ( ( v1_relat_1 @ B ) =>
% 17.15/17.35       ( r1_tarski @
% 17.15/17.35         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) @ 
% 17.15/17.35         ( k9_relat_1 @ ( k4_relat_1 @ B ) @ ( k9_relat_1 @ B @ A ) ) ) ))).
% 17.15/17.35  thf('92', plain,
% 17.15/17.35      (![X24 : $i, X25 : $i]:
% 17.15/17.35         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X24) @ X25) @ 
% 17.15/17.35           (k9_relat_1 @ (k4_relat_1 @ X24) @ (k9_relat_1 @ X24 @ X25)))
% 17.15/17.35          | ~ (v1_relat_1 @ X24))),
% 17.15/17.35      inference('cnf', [status(esa)], [t163_relat_1])).
% 17.15/17.35  thf('93', plain,
% 17.15/17.35      (((r1_tarski @ sk_A @ 
% 17.15/17.35         (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)))
% 17.15/17.35        | ~ (v1_relat_1 @ sk_B))),
% 17.15/17.35      inference('sup+', [status(thm)], ['91', '92'])).
% 17.15/17.35  thf('94', plain, ((v1_relat_1 @ sk_B)),
% 17.15/17.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.15/17.35  thf('95', plain,
% 17.15/17.35      ((r1_tarski @ sk_A @ 
% 17.15/17.35        (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 17.15/17.35      inference('demod', [status(thm)], ['93', '94'])).
% 17.15/17.35  thf('96', plain,
% 17.15/17.35      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 17.15/17.35        | ~ (v1_relat_1 @ sk_B))),
% 17.15/17.35      inference('sup+', [status(thm)], ['65', '95'])).
% 17.15/17.35  thf('97', plain, ((v1_relat_1 @ sk_B)),
% 17.15/17.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.15/17.35  thf('98', plain,
% 17.15/17.35      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 17.15/17.35      inference('demod', [status(thm)], ['96', '97'])).
% 17.15/17.35  thf('99', plain, ($false), inference('demod', [status(thm)], ['0', '98'])).
% 17.15/17.35  
% 17.15/17.35  % SZS output end Refutation
% 17.15/17.35  
% 17.15/17.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
